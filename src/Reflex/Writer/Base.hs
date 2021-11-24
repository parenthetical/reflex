-- | This module provides 'ReflexWriterT', the standard implementation of
-- 'Writer' for Reflex values.
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Writer.Base
  ( runReflexWriterT
  , ReflexWriterT
  , withReflexWriterT
  , mapReflexWriterT
  )
where

import Reflex.Adjustable.Class
import Reflex.Class
import Reflex.EventWriter.Class (EventWriter, tellEvent)
import Reflex.Dynamic (distributeDMapOverDynPure)
import Reflex.Host.Class
import Reflex.PerformEvent.Class
import Reflex.PostBuild.Class
import Reflex.Query.Class
import Reflex.Requester.Class
import Reflex.TriggerEvent.Class

import Control.Monad.Exception
import Control.Monad.Identity
import Control.Monad.Morph
import Control.Monad.Primitive
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State.Strict
import Control.Monad.Writer.Class
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Functor.Compose
import Data.Functor.Misc
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup
import Data.Some (Some)
import Data.Tuple
import Data.Type.Equality

import Unsafe.Coerce


-- TODO: Rename/needed/place?
class MConcatableF f w where
  mconcatf :: f [w] -> f w

instance (Reflex t, Semigroup w) => MConcatableF (Event t) w where
  mconcatf = mapMaybeCheap (fmap sconcat . nonEmpty)

instance (Reflex t, Monoid w) => MConcatableF (Behavior t) w where
  mconcatf = fmap mconcat

instance (Reflex t, Monoid w) => MConcatableF (Dynamic t) w where
  mconcatf = fmap mconcat


-- TODO: put Mergeable in appropriate place
class Mergeable (f :: * -> * -> *) t where
  mergef :: (Reflex t, GCompare k) => DMap k (f t) -> f t (DMap k Identity)

instance Mergeable Event t where
  mergef = merge

instance Mergeable Dynamic t where
  mergef = distributeDMapOverDynPure

instance Mergeable Behavior t where
  mergef = DMap.traverseWithKey (\_k v -> fmap Identity v)

{-# DEPRECATED TellId "Do not construct this directly; use tellId instead" #-}
newtype TellId w x
  = TellId Int -- ^ WARNING: Do not construct this directly; use 'tellId' instead
  deriving (Show, Eq, Ord, Enum)

tellId :: Int -> TellId w w
tellId = TellId
{-# INLINE tellId #-}

tellIdRefl :: TellId w x -> w :~: x
tellIdRefl _ = unsafeCoerce Refl

withTellIdRefl :: TellId w x -> (w ~ x => r) -> r
withTellIdRefl tid r = case tellIdRefl tid of
  Refl -> r

instance GEq (TellId w) where
  a `geq` b =
    withTellIdRefl a $
    withTellIdRefl b $
    if a == b
    then Just Refl
    else Nothing

instance GCompare (TellId w) where
  a `gcompare` b =
    withTellIdRefl a $
    withTellIdRefl b $
    case a `compare` b of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT

data ReflexWriterState f t w = ReflexWriterState
  { _reflexWriterState_nextId :: {-# UNPACK #-} !Int -- Always negative (and decreasing over time)
  , _reflexWriterState_told :: ![DSum (TellId w) (f t)] -- In increasing order
  }

-- | A basic implementation of 'Writer' for time-varying Reflex values.
newtype ReflexWriterT w f t m a = ReflexWriterT (StateT (ReflexWriterState f t w) m a)
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadTrans
    , MFunctor
    , MonadFix
    , MonadIO
    , MonadException
    , MonadAsyncException
    , MonadSample t
    , MonadRef
    , MonadAtomicRef
    , MonadHold t
    , PostBuild t
    , MonadReader r
    , MonadReflexCreateTrigger t
    )

-- | Run a 'ReflexWriterT' action.
runReflexWriterT :: forall f t m w a. (Semigroup w, Mergeable f t, Reflex t, Monad m, Functor (f t)) => ReflexWriterT w f t m a -> m (a, f t w)
runReflexWriterT (ReflexWriterT a) = do
  (result, requests) <- runStateT a $ ReflexWriterState (-1) []
  let combineResults :: DMap (TellId w) Identity -> w
      combineResults = sconcat
        . (\(h : t) -> h :| t) -- Unconditional; 'merge' guarantees that it will only fire with non-empty DMaps
        . DMap.foldlWithKey (\vs tid (Identity v) -> withTellIdRefl tid $ v : vs) [] -- This is where we finally reverse the DMap to get things in the correct order
  return (result, fmap combineResults $ mergef $ DMap.fromDistinctAscList $ _reflexWriterState_told requests) --TODO: We can probably make this fromDistinctAscList more efficient by knowing the length in advance, but this will require exposing internals of DMap; also converting it to use a strict list might help

instance (Reflex t, Functor (f t), Monad m, Semigroup w, Mergeable f t, Monoid (f t w)) => MonadWriter (f t w) (ReflexWriterT w f t m) where
  tell w = ReflexWriterT $ modify $ \old ->
    let myId = _reflexWriterState_nextId old
    in ReflexWriterState
       { _reflexWriterState_nextId = pred myId
       , _reflexWriterState_told = (tellId myId :=> w) : _reflexWriterState_told old
       }
  -- TODO: Is this correct, could it be more efficient?
  listen m = do
    (a,w) <- lift $ runReflexWriterT m
    tell w
    pure (a, w)
  pass m = do
    ((a,f),w) <- lift $ runReflexWriterT m
    tell (f w)
    pure a


-- | Given a function like 'runWithReplace' for the underlying monad, implement
-- 'runWithReplace' for 'ReflexWriterT'.  This is necessary when the underlying
-- monad doesn't have a 'Adjustable' instance or to override the default
-- 'Adjustable' behavior.
runWithReplaceReflexWriterTWith :: forall m f t w a b. ( MonadHold t m, Semigroup w
                                                       , Mergeable f t
                                                       , Monoid (f t w)
                                                       , Functor (f t)
                                                       , Switchable f t m
                                                       )
                               => (forall a' b'. m a' -> Event t (m b') -> ReflexWriterT w f t m (a', Event t b'))
                               -> ReflexWriterT w f t m a
                               -> Event t (ReflexWriterT w f t m b)
                               -> ReflexWriterT w f t m (a, Event t b)
runWithReplaceReflexWriterTWith f a0 a' = do
  (result0, result') <- f (runReflexWriterT a0) $ fmapCheap runReflexWriterT a'
  tell =<< lift (switchfE (snd result0) (fmapCheap snd result'))
  return (fst result0, fmapCheap fst result')

-- TODO: Type role/coercible magic needed for automatic deriving of Adjustable?
instance ( Adjustable t m, Monoid w, MonadHold t m, MonadFix m, Mergeable f t, Functor (f t), Monoid (f t w)
         , Switchable f t m
         , MConcatableF (f t) w
         ) => Adjustable t (ReflexWriterT w f t m) where
  runWithReplace = runWithReplaceReflexWriterTWith $ \dm0 dm' -> lift $ runWithReplace dm0 dm'
  traverseIntMapWithKeyWithAdjust = sequenceIntMapWithAdjustReflexWriterTWith (\f dm0 dm' -> lift $ traverseIntMapWithKeyWithAdjust f dm0 dm')
  traverseDMapWithKeyWithAdjust = sequenceDMapWithAdjustReflexWriterTWith (\f dm0 dm' -> lift $ traverseDMapWithKeyWithAdjust f dm0 dm') mapPatchDMap weakenPatchDMapWith switchfMapE
  traverseDMapWithKeyWithAdjustWithMove = sequenceDMapWithAdjustReflexWriterTWith (\f dm0 dm' -> lift $ traverseDMapWithKeyWithAdjustWithMove f dm0 dm') mapPatchDMapWithMove weakenPatchDMapWithMoveWith switchfMapWithMoveE

-- | Like 'runWithReplaceReflexWriterTWith', but for 'sequenceIntMapWithAdjust'.
sequenceIntMapWithAdjustReflexWriterTWith
  :: forall f t m w v v'
  .  (Mergeable f t, Monoid (f t w), MConcatableF (f t) w,
       Switchable f t m, Functor (f t), Monad m, Semigroup w)
  => (   (IntMap.Key -> v -> m (f t w, v'))
      -> IntMap v
      -> Event t (PatchIntMap v)
      -> ReflexWriterT w f t m (IntMap (f t w, v'), Event t (PatchIntMap (f t w, v')))
     )
  -> (IntMap.Key -> v -> ReflexWriterT w f t m v')
  -> IntMap v
  -> Event t (PatchIntMap v)
  -> ReflexWriterT w f t m (IntMap v', Event t (PatchIntMap v'))
sequenceIntMapWithAdjustReflexWriterTWith base f dm0 dm' = do
  let f' :: IntMap.Key -> v -> m (f t w, v')
      f' k v = swap <$> runReflexWriterT (f k v)
  (children0, children') <- base f' dm0 dm'
  let result0 = fmap snd children0
      result' = fmapCheap (fmap snd) children'
      requests0 :: IntMap (f t w)
      requests0 = fmap fst children0
      requests' :: Event t (PatchIntMap (f t w))
      requests' = fmapCheap (fmap fst) children'
  tell . mconcatf . fmap IntMap.elems =<< lift (switchfIntMapE requests0 requests')
  return (result0, result')

-- | Like 'runWithReplaceReflexWriterTWith', but for 'sequenceDMapWithAdjust'.
sequenceDMapWithAdjustReflexWriterTWith
  :: forall f t m p p' w k k11 v v'
  .  (Monoid (f t w), MConcatableF (f t) w, Semigroup w,
       Mergeable f t, Reflex t, Functor (f t), Monad m)
  => (   (forall a. k a -> v a -> m (Compose ((,) (f t w)) v' a))
      -> DMap k v
      -> Event t (p k v)
      -> ReflexWriterT w f t m (DMap k (Compose ((,) (f t w)) v'), Event t (p k (Compose ((,) (f t w)) v')))
     )
  -> ((forall a. Compose ((,) (f t w)) v' a -> v' a) -> p k (Compose ((,) (f t w)) v') -> p k v')
  -> ((forall a. Compose ((,) (f t w)) v' a -> f t w) -> p k (Compose ((,) (f t w)) v') -> p' (Some k) (f t w))
  -> (Map (Some k) (f t w) -> Event t (p' (Some k) (f t w)) -> m (f t (Map k11 w)))
  -> (forall a. k a -> v a -> ReflexWriterT w f t m (v' a))
  -> DMap k v
  -> Event t (p k v)
  -> ReflexWriterT w f t m (DMap k v', Event t (p k v'))
sequenceDMapWithAdjustReflexWriterTWith base mapPatch weakenPatchWith switchf f dm0 dm' = do
  let f' :: forall a. k a -> v a -> m (Compose ((,) (f t w)) v' a)
      f' k v = Compose . swap <$> runReflexWriterT (f k v)
  (children0, children') <- base f' dm0 dm'
  let result0 = DMap.map (snd . getCompose) children0
      result' = fforCheap children' $ mapPatch $ snd . getCompose
      requests0 :: Map (Some k) (f t w)
      requests0 = weakenDMapWith (fst . getCompose) children0
      requests' :: Event t (p' (Some k) (f t w))
      requests' = fforCheap children' $ weakenPatchWith $ fst . getCompose
  tell . mconcatf . fmap Map.elems =<< lift (switchf requests0 requests')
  return (result0, result')

-- TODO: Implement this using MonadTransControl (?).
-- | Map a function over the output of a 'ReflexWriterT'.
withReflexWriterT :: ( Monoid w, Monoid w', Reflex t, MonadHold t m, Mergeable f t, Functor (f t)
                     , Monoid (f t w')
                     )
                   => (w -> w')
                   -> ReflexWriterT w f t m a
                   -> ReflexWriterT w' f t m a
withReflexWriterT f dw = do
  (r, d) <- lift $ do
    (r, d) <- runReflexWriterT dw
    let d' = fmap f d
    return (r, d')
  tell d
  pure r

-- TODO: Implement this using MonadTransControl (?).
-- | Change the monad underlying an ReflexWriterT
mapReflexWriterT
  :: (forall x. m x -> n x)
  -> ReflexWriterT w f t m a
  -> ReflexWriterT w f t n a
mapReflexWriterT f (ReflexWriterT a) = ReflexWriterT $ mapStateT f a

-- TODO: Remove these implementations via deriving strategies etc.?
instance Requester t m => Requester t (ReflexWriterT w f t m) where
  type Request (ReflexWriterT w f t m) = Request m
  type Response (ReflexWriterT w f t m) = Response m
  requesting = lift . requesting
  requesting_ = lift . requesting_

instance EventWriter t w m => EventWriter t w (ReflexWriterT v f t m) where
  tellEvent = lift . tellEvent

instance PerformEvent t m => PerformEvent t (ReflexWriterT w f t m) where
  type Performable (ReflexWriterT w f t m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent = lift . performEvent

instance PrimMonad m => PrimMonad (ReflexWriterT w f t m) where
  type PrimState (ReflexWriterT w f t m) = PrimState m
  primitive = lift . primitive

instance (MonadQuery t q m, Monad m) => MonadQuery t q (ReflexWriterT w f t m) where
  tellQueryIncremental = lift . tellQueryIncremental
  askQueryResult = lift askQueryResult
  queryIncremental = lift . queryIncremental

instance TriggerEvent t m => TriggerEvent t (ReflexWriterT w f t m) where
  newTriggerEvent = lift newTriggerEvent
  newTriggerEventWithOnComplete = lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete = lift . newEventWithLazyTriggerWithOnComplete
