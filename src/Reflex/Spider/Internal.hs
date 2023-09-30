{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}

#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
{-# OPTIONS_GHC -Wunused-binds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections #-}
-- | This module is the implementation of the 'Spider' 'Reflex' engine.  It uses
-- a graph traversal algorithm to propagate 'Event's and 'Behavior's.
module Reflex.Spider.Internal (module Reflex.Spider.Internal) where

import Control.Applicative (liftA2)
import Control.Monad hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Identity hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Ref
import qualified Control.Monad.Fail as MonadFail
import Data.Foldable hiding (concat, elem, sequence_)
import Data.Maybe hiding (mapMaybe)
import Witherable (mapMaybe)
import GHC.Exts hiding (toList)
import Data.Type.Coercion
import Data.Profunctor.Unsafe ((#.), (.#))
import qualified Reflex.Class
import qualified Reflex.Class as R
import qualified Reflex.Host.Class
import Reflex.NotReady.Class
import Reflex.PerformEvent.Base (PerformEventT)
import Control.Concurrent
import Control.Exception
import Control.Monad.Catch (MonadMask, MonadThrow, MonadCatch)
import Control.Monad.Exception
import Control.Monad.Primitive
import Control.Monad.Reader.Class
import Control.Monad.ReaderIO
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Functor.Constant
import Data.Functor.Misc
import Data.Functor.Product
import Data.GADT.Compare
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IORef
import Data.Kind (Type)
import Data.Proxy
import Data.Traversable
import Data.Type.Equality ((:~:)(Refl))
import System.IO.Unsafe
import System.Mem.Weak
import Unsafe.Coerce
import Data.Reflection
import Data.Some (Some(Some))
import Data.WeakBag (WeakBag)
import qualified Data.WeakBag as WeakBag
import Data.Patch
import qualified Data.Patch.DMap as PatchDMap
import qualified Data.Patch.DMapWithMove as PatchDMapWithMove
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Data.Bool (bool)

type Behavior (x :: Type) a = R.Behavior (SpiderTimeline x) a
type Event (x :: Type) a = R.Event (SpiderTimeline x) a
type Incremental x p = R.Incremental (SpiderTimeline x) p

whenM :: Monad m => m Bool -> m () -> m ()
whenM mcond m = mcond >>= flip when m

--NB: Once you subscribe to an Event, you must always hold on the the WHOLE EventSubscription you get back
-- If you do not retain the subscription, you may be prematurely unsubscribed from the parent event.
data EventSubscription x = EventSubscription
  { unsubscribe :: !(IO ())
  , _eventSubscription_subscribed :: {-# UNPACK #-} !(EventSubscribed x)
  }

data Subscriber x a = Subscriber
  { subscriberPropagate :: !(a -> EventM x ())
  , subscriberInvalidateHeight :: !(Height -> IO ())
  , subscriberRecalculateHeight :: !(Height -> IO ())
  }

subscribe :: Event x a -> Subscriber x a -> EventM x (EventSubscription x)
subscribe e s = fst <$> subscribeAndRead e s

returnSubscription :: Monad m => IO () -> IORef Height -> a -> b -> m (EventSubscription x, b)
returnSubscription cleanup heightRef retained occ =
  return (EventSubscription cleanup (EventSubscribed heightRef (toAny retained)), occ)

subscribeWith :: HasSpiderTimeline x => Event x a -> (a -> EventM x b) -> Subscriber x a -> EventM x (EventSubscription x)
subscribeWith e f = subscribe (R.pushCheap (\a -> f a >> pure (Just a)) e)

{-# RULES
"cacheEvent/cacheEvent" forall e. cacheEvent (cacheEvent e) = cacheEvent e
"cacheEvent/pushCheap" forall f e. R.pushCheap f (cacheEvent e) = cacheEvent (R.pushCheap f e)
"buildIncremental/cacheEvent" forall f e. buildIncremental f (cacheEvent e) = buildIncremental f e
  #-}



-- | Construct an 'Event' whose value is guaranteed not to be recomputed
-- repeatedly
--
--TODO: Try a caching strategy where we subscribe directly to the parent when
--there's only one subscriber, and then build our own FastWeakBag only when a second
--subscriber joins
{-# NOINLINE [0] cacheEvent #-}
cacheEvent :: forall x a. (HasSpiderTimeline x, Defer Clear (EventM x)) => Event x a -> Event x a
cacheEvent e = unsafePerformIO $ do
  subscribers :: WeakBag (Subscriber x a) <- WeakBag.empty
  parentSubscriptionRef :: IORef (EventSubscription x) <- newIORef $ error "cacheEvent: parentRef uninitialized"
  occRef :: IORef (Maybe a) <- newIORef Nothing
  pure $ Event $ \sub -> {-# SCC "cacheEvent" #-} do
    whenM (liftIO (WeakBag.null subscribers)) $
      liftIO . writeIORef parentSubscriptionRef
      <=< subscribeWith e (writeAndScheduleClear occRef) $ Subscriber
          { subscriberPropagate = flip propagate subscribers
          , subscriberInvalidateHeight = WeakBag.traverse_ subscribers . invalidateSubscriberHeight
          , subscriberRecalculateHeight = WeakBag.traverse_ subscribers . recalculateSubscriberHeight
          }
    parentSub <- liftIO $ readIORef parentSubscriptionRef
    sln <- liftIO $ WeakBag.insert' sub subscribers $ unsubscribe parentSub
    returnSubscription (WeakBag.remove sln >> touch sln)
                       (eventSubscribedHeightRef $ _eventSubscription_subscribed parentSub)
                       (sln, parentSubscriptionRef)
                       <=< liftIO $ readIORef occRef

invalidateSubscriberHeight :: Height -> Subscriber x a -> IO ()
invalidateSubscriberHeight = flip subscriberInvalidateHeight

recalculateSubscriberHeight :: Height -> Subscriber x a -> IO ()
recalculateSubscriberHeight = flip subscriberRecalculateHeight

-- | Propagate everything at the current height
propagate :: forall x a. a -> WeakBag (Subscriber x a) -> EventM x ()
propagate a subscribers =
  -- Note: in the following traversal, we do not visit nodes that are added to the list during our traversal; they are new events, which will necessarily have full information already, so there is no need to traverse them
  --TODO: Should we check if nodes already have their values before propagating?  Maybe we're re-doing work
  WeakBag.traverse_ subscribers $ \s -> subscriberPropagate s a

toAny :: a -> Any
toAny = unsafeCoerce

-- Why do we use Any here, instead of just giving eventSubscribedRetained an
-- existential type? Sadly, GHC does not currently know how to unbox types
-- with existentially quantified fields. So instead we just coerce values
-- to type Any on the way in. Since we never coerce them back, this is
-- perfectly safe.
data EventSubscribed x = EventSubscribed
  { eventSubscribedHeightRef :: {-# UNPACK #-} !(IORef Height)
  , _eventSubscribedRetained :: {-# NOUNPACK #-} !Any
  }

-- TODO: what is really needed here?
data PullSubscribed x a
   = PullSubscribed { pullSubscribedValue :: !a
                    , pullSubscribedInvalidators :: !(IORef [Weak Invalidator])
                    , pullSubscribedOwnInvalidator :: !Invalidator
                    , pullSubscribedParents :: ![SomeBehaviorSubscribed x] -- Need to keep parent behaviors alive, or they won't let us know when they're invalidated
                    }

{-# INLINABLE pull #-}
pull :: forall x a. BehaviorM x a -> Behavior x a
pull a = unsafePerformIO $ do
  ref :: IORef (Maybe (PullSubscribed x a)) <- newIORef Nothing
  invsRef :: IORef [Weak Invalidator] <- newIORef []
  pure $ Behavior $ do
    subscribed <- liftIO (readIORef ref) >>= \case
      Just subscribed -> pure subscribed
      Nothing -> do
        let i = readIORef ref
                >>= mapM_ (const $ do
                              writeIORef ref Nothing
                              invalidate invsRef)
        wi <- liftIO $ mkWeakPtrWithDebug i
        parentsRef <- liftIO $ newIORef []
        (_, !holdInits) <- ask -- ask behavior hold inits
        aVal <- liftIO $ runReaderIO (unBehaviorM a) (Just (wi, parentsRef), holdInits)
        parents <- liftIO $ readIORef parentsRef
        let subscribed = PullSubscribed
              { pullSubscribedValue = aVal
              , pullSubscribedInvalidators = invsRef
              , pullSubscribedOwnInvalidator = i
              , pullSubscribedParents = parents
              }
        liftIO $ writeIORef ref $ Just subscribed
        return subscribed
    addParentBAndInvalidator (BehaviorSubscribedPull subscribed) invsRef
    pure $ pullSubscribedValue subscribed

type BehaviorEnv x = (Maybe (Weak Invalidator, IORef [SomeBehaviorSubscribed x]), IORef [SomeInit x])

-- BehaviorM can sample behaviors
newtype BehaviorM (x :: Type) a = BehaviorM { unBehaviorM :: ReaderIO (BehaviorEnv x) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadReader (BehaviorEnv x))

data BehaviorSubscribed x a
   = BehaviorSubscribedHold (IORef (Maybe (EventSubscription x)))
   | BehaviorSubscribedPull (PullSubscribed x a)

newtype SomeBehaviorSubscribed x = SomeBehaviorSubscribed (Some (BehaviorSubscribed x))

-- type role PullSubscribed representational nominal

type Invalidator = IO ()

runBehaviorM :: BehaviorM x a -> Maybe (Weak Invalidator, IORef [SomeBehaviorSubscribed x]) -> IORef [SomeInit x] -> IO a
runBehaviorM a mwi holdInits = runReaderIO (unBehaviorM a) (mwi, holdInits)

-- TODO: What is the meaning of this function?
addParentBAndInvalidator :: BehaviorSubscribed x a -> IORef [Weak Invalidator] -> BehaviorM x ()
addParentBAndInvalidator h invsRef = do
  (!m, _) <- ask
  forM_ m $ \(!wi, !p) -> do
      liftIO $ modifyIORef' invsRef (wi:)
      liftIO $ modifyIORef' p (SomeBehaviorSubscribed (Some h) :)

dynamicConst :: HasSpiderTimeline x => PatchTarget p -> R.Incremental (SpiderTimeline x) p
dynamicConst !a = Incremental (R.constant a) R.never

-- | A statically allocated 'SpiderTimeline'
data Global

{-# NOINLINE globalSpiderTimelineEnv #-}
globalSpiderTimelineEnv :: SpiderTimelineEnv Global
globalSpiderTimelineEnv = unsafePerformIO unsafeNewSpiderTimelineEnv

-- | Stores all global data relevant to a particular Spider timeline; only one
-- value should exist for each type @x@
newtype SpiderTimelineEnv (x :: Type) = STE {unSTE :: SpiderTimelineEnv' x}
-- We implement SpiderTimelineEnv with a newtype wrapper so
-- we can get the coercions we want safely.
type role SpiderTimelineEnv nominal

data SpiderTimelineEnv' x = SpiderTimelineEnv
  { _spiderTimeline_lock :: {-# UNPACK #-} !(MVar ())
  , _spiderTimeline_eventEnv :: {-# UNPACK #-} !(EventEnv x)
  }

-- type role SpiderTimelineEnv' nominal

instance Eq (SpiderTimelineEnv x) where
  _ == _ = True -- Since only one exists of each type

instance GEq SpiderTimelineEnv where
  a `geq` b = if _spiderTimeline_lock (unSTE a) == _spiderTimeline_lock (unSTE b)
              then Just $ unsafeCoerce Refl -- This unsafeCoerce is safe because the same SpiderTimelineEnv can't have two different 'x' arguments
              else Nothing

data EventEnv x
   = EventEnv { eventEnvAssignments :: !(IORef [SomeAssignment x]) -- Needed for Subscribe  -- This should only actually get used when events are firing
              , eventEnvMergeUpdates :: !(IORef [MergeUpdate x])
              , eventEnvInits :: !(IORef [SomeInit x]) -- Needed for Subscribe
              , eventEnvClears :: !(IORef [Clear]) -- Needed for Subscribe
              , eventEnvCurrentHeight :: !(IORef Height) -- Needed for Subscribe
              , eventEnvDelayedMerges :: !(IORef (IntMap [EventM x ()]))
              }

asksEventEnv :: forall x a. HasSpiderTimeline x => (EventEnv x -> a) -> EventM x a
asksEventEnv f = return $ f $ _spiderTimeline_eventEnv (unSTE (spiderTimeline :: SpiderTimelineEnv x))

class MonadIO m => Defer a m where
  getDeferralQueue :: m (IORef [a])

{-# INLINE defer #-}
defer :: Defer a m => a -> m ()
defer a = do
  q <- getDeferralQueue
  liftIO $ modifyIORef' q (a:)

instance Defer (SomeInit x) (BehaviorM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = BehaviorM $ asks snd

instance HasSpiderTimeline x => Defer (SomeAssignment x) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvAssignments

instance HasSpiderTimeline x => Defer (MergeUpdate x) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvMergeUpdates

instance HasSpiderTimeline x => Defer (SomeInit x) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvInits

-- TODO: this is only used in the 'merge' function thus obfuscates what's going on?
class HasSpiderTimeline x => HasCurrentHeight x m | m -> x where
  getCurrentHeight :: m Height
  scheduleMerge :: Height -> EventM x () -> m ()

instance HasSpiderTimeline x => HasCurrentHeight x (EventM x) where
  {-# INLINE getCurrentHeight #-}
  getCurrentHeight = do
    heightRef <- asksEventEnv eventEnvCurrentHeight
    liftIO $ readIORef heightRef
  {-# INLINE scheduleMerge #-}
  scheduleMerge height subscribed = do
    delayedRef <- asksEventEnv eventEnvDelayedMerges
    liftIO $ modifyIORef' delayedRef $ IntMap.insertWith (++) (unHeight height) [subscribed]

class HasSpiderTimeline x where
  -- | Retrieve the current SpiderTimelineEnv
  spiderTimeline :: SpiderTimelineEnv x

instance HasSpiderTimeline Global where
  spiderTimeline = globalSpiderTimelineEnv

instance HasSpiderTimeline x => Defer Clear (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvClears

{-# INLINE writeAndScheduleClear #-}
writeAndScheduleClear :: Defer Clear m => IORef (Maybe a) -> a -> m ()
writeAndScheduleClear ref val = do
  liftIO $ writeIORef ref (Just val)
  defer $ Clear $ writeIORef ref Nothing

data MergeUpdate x = MergeUpdate
  { _mergeUpdate_update :: !(EventM x [EventSubscription x])
  , _mergeUpdate_invalidateHeight :: !(IO ())
  , _mergeUpdate_recalculateHeight :: !(IO ())
  }

newtype SomeInit x = SomeInit { unSomeInit :: EventM x () }

-- EventM can do everything BehaviorM can, plus create holds
newtype EventM x a = EventM { runEventM :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadException, MonadAsyncException, MonadCatch, MonadThrow, MonadMask)

data EvD x res =
  EvD { _heightRef :: IORef Height
      , _subscriptionsCtr :: IORef Int
      , _subscriptionsRef :: IORef (IntMap (EventSubscription x))
      , _sub :: Subscriber x res
      }

type EvM x res a = ReaderT (EvD x res) (EventM x) a

heightInvalidator :: EvM x res (IO ())
heightInvalidator = do
  heightRef <- asks _heightRef
  sub <- asks _sub
  pure $ do
    oldHeight <- readIORef heightRef
    -- Don't do anything if the height is already invalid
    when (oldHeight /= invalidHeight) $ do
      writeIORef heightRef $! invalidHeight
      subscriberInvalidateHeight sub oldHeight

heightUpdater :: EvM x res (IO ())
heightUpdater = do
  heightRef <- asks _heightRef
  subscriptionsRef <- asks _subscriptionsRef
  sub <- asks _sub
  pure $ do
    currentHeight <- readIORef heightRef
    -- recalculateMyHeight may be called multiple times; perhaps the's a way to finesse it to avoid this check
    -- TODO: This will almost always be true; can we get rid of this check and just proceed to the next one always?
    when (currentHeight == invalidHeight) $ do
      maybeNewHeight <- do
        subs <- mapM (readIORef . eventSubscribedHeightRef . _eventSubscription_subscribed) . IntMap.elems =<< readIORef subscriptionsRef
        -- TODO: succHeight is not needed for coincidence/switch
        pure $ if invalidHeight `elem` subs then invalidHeight else let (Height h) = maximum (zeroHeight:subs) in Height (succ h)
      when (maybeNewHeight /= invalidHeight) $ do
        writeIORef heightRef $! maybeNewHeight
        subscriberRecalculateHeight sub maybeNewHeight

subscribeAndRead_ :: forall x res a. Defer (MergeUpdate x) (EventM x) => Event x a -> Subscriber x a -> EvM x res (IO (), Maybe a)
subscribeAndRead_ e subscriber = do
  heightRef <- asks _heightRef
  subscriptionsCtr <- asks _subscriptionsCtr
  subscriptionsRef <- asks _subscriptionsRef
  invalidateMyHeight <- heightInvalidator
  recalculateMyHeight <- heightUpdater
  (subscription, occ) <- lift $ subscribeAndRead e subscriber
  i <- liftIO $ atomicModifyIORef subscriptionsCtr (\i -> (succ i, i))
  liftIO $ modifyIORef subscriptionsRef (IntMap.insert i subscription)
  liftIO $ writeIORef heightRef invalidHeight
  liftIO recalculateMyHeight
  pure ( runEventM @x $ do
              liftIO $ modifyIORef subscriptionsRef (IntMap.delete i)
              defer $ MergeUpdate @x (pure [subscription])
                        invalidateMyHeight
                        recalculateMyHeight
       , occ
       )

subscriber_ :: EvM x res (Subscriber x res)
subscriber_ = do
  invalidateMyHeight <- heightInvalidator
  recalculateMyHeight <- heightUpdater
  sub <- asks _sub
  pure $ Subscriber
            { subscriberPropagate = subscriberPropagate sub
            , subscriberInvalidateHeight = const invalidateMyHeight
            , subscriberRecalculateHeight = const recalculateMyHeight
            }

toEvent :: Height -> EvM x res (IO (), b, Maybe res) -> Event x res
toEvent initHeight evM = Event $ \sub -> do
  heightRef <- liftIO $ newIORef initHeight -- TODO: why is this messed up? (switch fails with zeroHeight)
  subscriptionsCtr :: IORef Int <- liftIO $ newIORef 0
  subscriptionsRef :: IORef (IntMap (EventSubscription x)) <- liftIO $ newIORef IntMap.empty
  (unsubscribeExtra, retainExtra, occ) <- runReaderT evM (EvD heightRef subscriptionsCtr subscriptionsRef sub)
  returnSubscription
    (do mapM_ unsubscribe =<< readIORef subscriptionsRef
        unsubscribeExtra)
    heightRef
    (subscriptionsRef, retainExtra)
    occ

coincidence :: forall x a. (HasSpiderTimeline x, Defer (MergeUpdate x) (EventM x), Defer Clear (EventM x)) => Event x (Event x a) -> Event x a
coincidence coincidenceParent = cacheEvent $ toEvent zeroHeight $ do
  evD <- ask
  (_unsubscribeOuterSubscription, occ) <-
    subscribeAndRead_ (R.pushCheap (\e -> do
                                     -- This is: "subscribe for one frame"
                                     (doUnsubscribe, occ) <- runReaderT (subscribeAndRead_ e =<< subscriber_) evD
                                     liftIO doUnsubscribe
                                     return occ)
                       coincidenceParent)
      =<< subscriber_
  pure (pure (), (), occ)

-- TODO: can switch be written using something like unsafeUpdated and tellEvent?
switch :: forall x a. HasSpiderTimeline x => Behavior x (Event x a) -> Event x a
switch switchParent = cacheEvent $ toEvent invalidHeight $ do
  ownWeakInvalidatorRef :: IORef (Weak Invalidator) <- liftIO $ newIORef $ error "switch: ownWeakInvalidatorRef uninitialized"
  evD <- ask
  let writeNewWeakInvalidator i = do
        wi <- mkWeakPtrWithDebug i
        writeIORef ownWeakInvalidatorRef $! wi
  liftIO $ writeNewWeakInvalidator (pure ())
  ownInvalidatorRef <- liftIO $ newIORef $ error "switch: ownInvalidatorRef uninitialized"
  -- withB is like "fold over Behavior updates"
  let withB :: forall s b c. s -> Behavior x b -> (s -> b -> EvM x a (s, c)) -> EvM x a (s, c)
      withB currentState b f = mfix $ \(~(newState, _)) -> do
       let ownInvalidator = runEventM @x $ defer $ Clear $ do
                    putStrLn "Running inits inside switch"
                    -- TODO: this used to be runFrame instead of justRunInits but in the tests only inits are generated, also it now loops if you use runFrame (if you defer to MergeUpdate it doesn't loop).
                    unSpiderHost . justRunInits $ void $ runReaderT (withB newState b f) evD
       liftIO $ writeIORef ownInvalidatorRef ownInvalidator
       liftIO $ finalize =<< readIORef ownWeakInvalidatorRef
       liftIO $ writeNewWeakInvalidator ownInvalidator
       f currentState <=< liftIO $ do
         wi <- readIORef ownWeakInvalidatorRef
         initsRef <- newIORef [] -- TODO: normally initsRef <- getDeferralQueue, but here the initsRef stays empty?
         parentsRef <- newIORef []
         runBehaviorM (R.sample b) (Just (wi, parentsRef)) initsRef
  ~(_, parentOcc) <- withB (pure ()) switchParent $ \unsubscribePrevious e -> do
        liftIO unsubscribePrevious
        subscribeAndRead_ e =<< subscriber_
  pure ( finalize =<< readIORef ownWeakInvalidatorRef -- We don't need to get invalidated if we're dead
       , ownInvalidatorRef -- TODO: what exactly should go here?
       , parentOcc
       )

-- Propagate the given event occurrence; before cleaning up, run the given action, which may read the state of events and behaviors
run :: forall x b. HasSpiderTimeline x => [DSum (RootTrigger x) Identity] -> EventM x b -> SpiderHost x b
run roots after = do
  let t = spiderTimeline :: SpiderTimelineEnv x
  SpiderHost $ withMVar (_spiderTimeline_lock (unSTE t)) $ \_ -> unSpiderHost $ runFrame $ do
    rootsToPropagate <- forM roots $ \r@(RootTrigger (_, occRef, k) :=> a) -> do
      occBefore <- liftIO $ do
        occBefore <- readIORef occRef
        writeIORef occRef $! DMap.insert k a occBefore
        return occBefore
      if DMap.null occBefore
        then do defer $ Clear $ rootClear occRef
                return $ Just r
        else return Nothing
    forM_ (catMaybes rootsToPropagate) $ \(RootTrigger (subscribersRef, _, _) :=> Identity a) -> do
      propagate a subscribersRef
    delayedRef <- asksEventEnv eventEnvDelayedMerges
    let putCurrentHeight h = do
          heightRef <- asksEventEnv eventEnvCurrentHeight
          liftIO $ writeIORef heightRef $! h
    fix $ \go -> do
          delayed <- liftIO $ readIORef delayedRef
          forM_ (IntMap.minViewWithKey delayed) $ \((currentHeight, cur), future) -> do
              putCurrentHeight $ Height currentHeight
              liftIO $ writeIORef delayedRef $! future
              sequence_ cur
              go
    putCurrentHeight maxBound
    after

newtype Clear = Clear (IO ())

data SomeAssignment x = forall a. SomeAssignment {-# UNPACK #-} !(IORef a) {-# UNPACK #-} !(IORef [Weak Invalidator]) a

mkWeakPtrWithDebug :: a -> IO (Weak a)
mkWeakPtrWithDebug x = mkWeakPtr x Nothing

data EventLoopException = EventLoopException
instance Exception EventLoopException

instance Show EventLoopException where
  show EventLoopException = "causality loop detected: \n" <>
    "compile reflex with flag 'debug-cycles' and compile with profiling enabled for stack tree"

-- Always refers to 0
{-# NOINLINE zeroRef #-}
zeroRef :: IORef Height
zeroRef = unsafePerformIO $ newIORef zeroHeight

fanG :: forall x k v. (HasSpiderTimeline x, GCompare k) => Event x (DMap k v) -> EventSelectorG x k v
fanG =
  fan
  (DMap.null :: (DMap k (FanSubscribedChildren x k v) -> Bool))
  (\f subscribers -> forM_ (DMap.toList subscribers) $ \(_ :=> v) ->
              WeakBag.traverse_ (_fanSubscribedChildren v) f)
  (\f -> EventSelectorG $ \(!k) -> unsafeCoerce f
    ( fmap _fanSubscribedChildren . DMap.lookup k
    , DMap.lookup k
    , DMap.insert k . FanSubscribedChildren
    , DMap.delete k
    , \a subs ->
         void
         $ DMap.traverseWithKey (\_ (Pair v subsubs) -> do
                                          propagate @x v $ _fanSubscribedChildren subsubs
                                          return $ Constant ())
         $ DMap.intersectionWithKey @k (const Pair) a subs
    ))

fanInt :: HasSpiderTimeline x => Event x (IntMap a) -> EventSelectorInt x a
fanInt =
  fan
  IntMap.null
  (\f subscribers -> forM_ (IntMap.elems subscribers) $ \v -> WeakBag.traverse_ v f)
  (\f -> EventSelectorInt $ \(!k) -> f
     ( IntMap.lookup k
     , IntMap.lookup k
     , IntMap.insert k
     , IntMap.delete k
     , \a -> sequence_ . IntMap.intersectionWith propagate a
     ))

-- TODO: this currently uses something like "IntMap (WeakBag (Subscriber x a))" for subscribers, but wouldn't it be possible to use "IntMap (Subscriber x a)" paired with a cacheEvent for each selected key?
{-# INLINE fan #-}
fan :: forall {a1} {x1} {a2} {a3}
       {a5}.
  (Monoid a1, HasSpiderTimeline x1) =>
  (a1 -> Bool)
  -> ((forall a. Subscriber x1 a -> IO ()) -> a1 -> IO ())
  -> (((a1 -> Maybe (WeakBag (Subscriber x1 a2)),
        a3 -> Maybe a2,
        WeakBag (Subscriber x1 a2) -> a1 -> a1,
        a1 -> a1,
        a3 -> a1 -> EventM x1 ()) -> Event x1 a2)
      -> a5)
  -> Event x1 a3
  -> a5
fan isNull traverseWeakBags eventSelector e = unsafePerformIO $ do
  -- TODO: no need for Maybe in parentSubscriptionRef? Can do things unsafely instead
  -- This is the subscription which will update occRef:
  subscribersRef <- newIORef mempty
  parentSubscriptionRef <- newIORef $ error "fanG: no subscription"
  occRef <- newIORef Nothing
  pure $ eventSelector $ \(lookup,lookup2,insert,delete,doPropagation) -> Event $ \sub -> do
    whenM (liftIO $ isNull <$> readIORef subscribersRef) $ do
      -- Not initialized: subscribe to parent.
      liftIO . writeIORef parentSubscriptionRef
      <=< subscribeWith e (writeAndScheduleClear occRef)
        $ Subscriber
        { subscriberPropagate = \a -> doPropagation a <=< liftIO $ readIORef subscribersRef
        , subscriberInvalidateHeight = \old ->
            traverseWeakBags (invalidateSubscriberHeight old) =<< readIORef subscribersRef
        , subscriberRecalculateHeight = \new ->
            traverseWeakBags (recalculateSubscriberHeight new) =<< readIORef subscribersRef
        }
    sln <- liftIO $ do
      subscribers <- readIORef subscribersRef
      list <- flip fromMaybe (pure <$> lookup subscribers) $ {-# SCC "missSubscribeFanSubscribed" #-} do
          -- No WeakBag of subscribers yet for this key:
          list <- WeakBag.empty
          writeIORef subscribersRef $! insert list subscribers
          pure list
      WeakBag.insert' sub list $ do -- called when the WeakBag for a key is empty:
        reducedSubscribers <- delete <$> readIORef subscribersRef
        writeIORef subscribersRef $! reducedSubscribers
        -- When we don't have any subscribers, unsubscribe from e
        when (isNull reducedSubscribers) $ do
          unsubscribe =<< readIORef parentSubscriptionRef
          writeIORef parentSubscriptionRef (error "fanG: parentSubscriptionRef emptied")
    subscribedParent <- liftIO $ _eventSubscription_subscribed <$> readIORef parentSubscriptionRef
    returnSubscription (WeakBag.remove sln >> touch sln)
             (eventSubscribedHeightRef subscribedParent)
             (sln, parentSubscriptionRef)
       . (lookup2 =<<)
       =<< liftIO (readIORef occRef)

newtype EventSelector x k = EventSelector { select :: forall a. k a -> Event x a }
newtype EventSelectorG x k v = EventSelectorG { selectG :: forall a. k a -> Event x (v a) }

newtype FanSubscribedChildren x k v a = FanSubscribedChildren
  { _fanSubscribedChildren :: WeakBag (Subscriber x (v a))
  }

newtype EventSelectorInt x a = EventSelectorInt { selectInt :: Int -> Event x a }

mergeInt :: forall x a. (HasSpiderTimeline x) => Incremental x (PatchIntMap (Event x a)) -> Event x (IntMap a)
mergeInt =
  merge
  (\tellE ipt -> IntMap.traverseWithKey (\k v -> tellE (IntMap.singleton k <$> v)) ipt)
  (\tellE (PatchIntMap ip) s -> do
     ip' <- IntMap.traverseWithKey (\k ->mapM (tellE . fmap (IntMap.singleton k))) ip
     sequence_ $ IntMap.intersection s ip
     pure $ applyAlways (PatchIntMap ip') s)

{-# INLINE mergeG' #-}
mergeG' :: forall k q x v patch. (HasSpiderTimeline x, GCompare k, PatchTarget (patch k q) ~ DMap k q, Patch (patch k q))
  => ( TellE x (DMap k v)
       -> patch k q
       -> DMap k (Constant (EventM x ()))
       -> EventM x (DMap k (Constant (EventM x ()))))
  -> (forall a. q a -> Event x (v a))
  -> Incremental x (patch k q)
  -> Event x (DMap k v)
mergeG' doPatch nt =
  merge
  (\tellE ipt -> DMap.traverseWithKey (\k v -> Constant <$> tellE (DMap.singleton k <$> nt v)) ipt)
  doPatch

mergeG :: forall k q x v. (HasSpiderTimeline x, GCompare k)
  => (forall a. q a -> Event x (v a)) -> Incremental x (PatchDMap k q) -> Event x (DMap k v)
mergeG nt =
  mergeG'
  (\tellE ip s -> do
     ip' <- traversePatchDMapWithKey (\k v -> Constant <$> tellE (DMap.singleton k <$> nt v))
            ip
     mapM_ (\(_ :=> v) -> getConstant v) . DMap.toList $ PatchDMap.getDeletions ip s
     pure $ applyAlways ip' s)
  nt

mergeWithMove :: forall k x v q. (HasSpiderTimeline x, GCompare k)
  => (forall a. q a -> Event x (v a)) -> Incremental x (PatchDMapWithMove k q) -> Event x (DMap k v)
mergeWithMove nt =
  mergeG'
  (\tellE ip s -> do
     ip' <- traversePatchDMapWithMoveWithKey (\k v ->
                               Constant <$> tellE (DMap.singleton k <$> nt v))
            ip
     sequence_ $ mapMaybe (\(_ :=> v) -> getConstant v)
          $ DMap.toList
          $ DMap.intersectionWithKey
            (\_ to (Constant unsub) ->
                Constant $ case getComposeMaybe to of
                  Nothing -> -- We are deleting/replacing
                    Just unsub
                  Just _toKey -> do -- We are moving
                    Nothing)
            (DMap.map PatchDMapWithMove._nodeInfo_to . unPatchDMapWithMove $ ip')
            s
     pure $ applyAlways ip' s)
  nt

type TellE x a = Event x a -> EventM x (EventM x ())

-- TODO: merge scheduling used to check this; useful for debugging but needs special casing so I left it out:
-- case height `compare` currentHeight of
--   LT -> error "Somehow a merge's height has been decreased after it was scheduled"
{-# INLINE merge #-}
merge :: forall x ip ipt o s.
  ( HasSpiderTimeline x, PatchTarget ip ~ ipt, Monoid o, Patch ip)
  => (TellE x o -> ipt -> EventM x s)
  -> (TellE x o -> ip -> s -> EventM x s)
  -> Incremental x ip -- p is the type of DMap Patch (i.e. With/Without Move)
  -> Event x o
merge doInitialInput doPatchInput d = cacheEvent $ toEvent zeroHeight $ do
  accumRef :: IORef o <- liftIO $ newIORef mempty
  heightRef <- asks _heightRef
  sub <- asks _sub
  evD <- ask
  recalculateMyHeight <- heightUpdater
  invalidateMyHeight <- heightInvalidator
  anEventFiredRef <- liftIO $ newIORef False
  let seenAllEvents = do
        height <- liftIO $ readIORef heightRef
        currentHeight <- getCurrentHeight
        pure (height <= currentHeight)
  let mergeSubscribeAndRead :: Event x o -> EventM x (EventM x ())
      mergeSubscribeAndRead e =
        runReaderT (liftIO . fst <$> subscribeAndRead_ 
          (R.pushCheap (\a -> do
               didAnEventFire <- liftIO $ atomicModifyIORef anEventFiredRef (True,)
               liftIO $ modifyIORef accumRef (a <>) -- maps are left-biased generally but there shouldn't be dup'd keys anyway
               liftIO $ do height <- readIORef heightRef
                           when (height == invalidHeight) $
                             throwIO EventLoopException
               unless didAnEventFire $ do -- Only schedule the firing once
                 let scheduleMerge' initialHeight = scheduleMerge initialHeight $ do
                       seenAllEvents >>= bool (scheduleMerge' =<< liftIO (readIORef heightRef)) (do
                           initPhaseDidntReturnOcc <- liftIO (readIORef anEventFiredRef)
                           when initPhaseDidntReturnOcc $ do
                           -- Once we're done with this, we can clear it immediately, because if there's a cacheEvent in front of us,
                           -- it'll handle subsequent subscribers, and if not, we won't get subsequent subscribers
                             liftIO $ writeIORef anEventFiredRef False
                             subscriberPropagate sub =<< liftIO (atomicModifyIORef accumRef (mempty,)))
                 scheduleMerge' <=< liftIO $ readIORef heightRef
               pure (Just ()))
           e)
          (Subscriber (const (pure ())) (const invalidateMyHeight) (const recalculateMyHeight)))
        evD
  initialState <- lift $ doInitialInput mergeSubscribeAndRead
                         =<< R.sample (incrementalCurrent d)
  stateB <- mfix $ \stateB -> R.hold initialState
                              . R.pushCheap (\p -> do
                                                oldState <- R.sample stateB
                                                Just <$> doPatchInput mergeSubscribeAndRead p oldState)
                           $ R.updatedIncremental d
  occ <- runMaybeT $ do
       -- TODO: this is the same logic as in 'scheduleMerge''
       guard =<< lift (lift seenAllEvents)
       guard =<< liftIO (readIORef anEventFiredRef)
       liftIO $ writeIORef anEventFiredRef False
       liftIO $ atomicModifyIORef accumRef (mempty,)
  pure ( pure ()
       , stateB -- TODO: without this GC-semantics tests fail, but how can it be automated?
       , occ
       )

invalidate :: IORef [Weak Invalidator] -> IO ()
invalidate wisRef = do
  wis <- readIORef wisRef
  forM_ wis $ \wi -> do
    mi <- deRefWeak wi
    case mi of
      Nothing -> pure () --TODO: Should we clean this up here?
      Just i -> do
        finalize wi -- Once something's invalidated, it doesn't need to hang around; this will change when some things are strict
        i
  writeIORef wisRef []

rootClear :: IORef (DMap k v) -> IO ()
rootClear ref = writeIORef ref $! DMap.empty

justRunInits :: forall x a. HasSpiderTimeline x => EventM x a -> SpiderHost x a --TODO: This function also needs to hold the mutex
justRunInits a = SpiderHost $ do
  let env = _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  runEventM $ do
        result <- a
        -- This must happen before doing the assignments, in case subscribing a Hold causes existing Holds to be read by the newly-propagated events:
        fix $ \runInits -> do
          inits <- liftIO $ readIORef (eventEnvInits env)
          unless (null inits) $ do
            liftIO $ writeIORef (eventEnvInits env) []
            forM_ inits unSomeInit
            runInits
        return result

-- | Run an event action outside of a frame
runFrame :: forall x a. HasSpiderTimeline x => EventM x a -> SpiderHost x a --TODO: This function also needs to hold the mutex
runFrame a = SpiderHost $ do
  let (EventEnv toAssignRef mergeUpdateRef initRef toClearRef heightRef delayedRef) =
        _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  result <- unSpiderHost $ justRunInits a
  readIORef toAssignRef >>= mapM_ (\(SomeAssignment vRef iRef v) -> do
                                                    writeIORef vRef v
                                                    invalidate iRef)
  readIORef toClearRef >>= mapM_ (\(Clear m) -> m)
  mergeUpdates <- readIORef mergeUpdateRef
  do writeIORef toAssignRef []
     writeIORef mergeUpdateRef []
     writeIORef initRef []
     writeIORef heightRef zeroHeight
     writeIORef toClearRef []
     writeIORef delayedRef IntMap.empty
  liftIO . mapM_ unsubscribe =<< runEventM (concat <$> mapM _mergeUpdate_update mergeUpdates)
  mapM_ _mergeUpdate_invalidateHeight mergeUpdates --TODO: In addition to when the patch is completely empty, we should also not run this if it has some Nothing values, but none of them have actually had any effect; potentially, we could even check for Just values with no effect (e.g. by comparing their IORefs and ignoring them if they are unchanged); actually, we could just check if the new height is different
  mapM_ _mergeUpdate_recalculateHeight mergeUpdates
  return result

newtype Height = Height { unHeight :: Int } deriving (Show, Read, Eq, Ord, Bounded)

{-# INLINE zeroHeight #-}
zeroHeight :: Height
zeroHeight = Height 0

{-# INLINE invalidHeight #-}
invalidHeight :: Height
invalidHeight = Height (-1000)

unsafeNewSpiderTimelineEnv :: forall x. IO (SpiderTimelineEnv x)
unsafeNewSpiderTimelineEnv = do
  lock <- newMVar ()
  env <- do toAssignRef <- newIORef []
            mergeUpdateRef <- newIORef []
            initRef <- newIORef []
            heightRef <- newIORef zeroHeight
            toClearRef <- newIORef []
            delayedRef <- newIORef IntMap.empty
            return $ EventEnv toAssignRef mergeUpdateRef initRef toClearRef heightRef delayedRef
  return $ STE $ SpiderTimelineEnv
    { _spiderTimeline_lock = lock
    , _spiderTimeline_eventEnv = env
    }

-- | Create a new SpiderTimelineEnv
newSpiderTimeline :: IO (Some SpiderTimelineEnv)
newSpiderTimeline = withSpiderTimeline (pure . Some)

data LocalSpiderTimeline (x :: Type) s

instance Reifies s (SpiderTimelineEnv x) =>
         HasSpiderTimeline (LocalSpiderTimeline x s) where
  spiderTimeline = localSpiderTimeline Proxy $ reflect (Proxy :: Proxy s)

localSpiderTimeline
  :: proxy s
  -> SpiderTimelineEnv x
  -> SpiderTimelineEnv (LocalSpiderTimeline x s)
localSpiderTimeline _ = coerce

-- | Pass a new timeline to the given function.
withSpiderTimeline :: forall r. (forall x. HasSpiderTimeline x => SpiderTimelineEnv x -> IO r) -> IO r
withSpiderTimeline k = do
  env <- unsafeNewSpiderTimelineEnv
  reify env $ \s -> k $ localSpiderTimeline s env

data RootTrigger x a = forall k. GCompare k => RootTrigger (WeakBag (Subscriber x a), IORef (DMap k Identity), k a)

data SpiderEventHandle x a = SpiderEventHandle
  { spiderEventHandleSubscription :: EventSubscription x
  , spiderEventHandleValue :: IORef (Maybe a)
  }

-- | The monad for actions that manipulate a Spider timeline identified by @x@
newtype SpiderHost (x :: Type) a = SpiderHost { unSpiderHost :: IO a } deriving (Functor, Applicative, MonadFix, MonadIO, MonadException, MonadAsyncException)

instance Monad (SpiderHost x) where
  {-# INLINABLE (>>=) #-}
  SpiderHost x >>= f = SpiderHost $ x >>= unSpiderHost . f

data NewFanSubscribedChildren x a = NewFanSubscribedChildren
  { _newFanSubscribedChildren :: WeakBag (Subscriber x a)
  , _newFanSubscribedUninit :: IO ()
  }

-- TODO: anything in common with Fan?
newFanEventWithTriggerIO :: forall x k. (GCompare k) => (forall a. k a -> RootTrigger x a -> IO (IO ())) -> IO (EventSelector x k)
newFanEventWithTriggerIO f = do
  occRef <- newIORef DMap.empty
  subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  return $ EventSelector $ \(!k) -> Event $ \sub -> liftIO $ do
    (NewFanSubscribedChildren subscribers uninit) <- readIORef subscribedRef >>= (\case
      Just res -> {-# SCC "hitRoot" #-} pure res
      Nothing -> {-# SCC "missRoot" #-} do
        subscribers <- WeakBag.empty
        uninit <- f k $ RootTrigger (subscribers, occRef, k)
        let res = NewFanSubscribedChildren subscribers uninit
        modifyIORef' subscribedRef $ DMap.insertWith (error "getRootSubscribed: duplicate key inserted into Root") k res
        pure res) . DMap.lookup k
    sln <- WeakBag.insert' sub subscribers $ do
              uninit
              modifyIORef' subscribedRef $ DMap.delete k
    -- TODO: understand original intent of this comment:
    -- If we die at the same moment that all our children die, they will
    -- try to clean us up but will fail because their Weak reference to us
    -- will also be dead.  So, if we are dying, check if there are any
    -- children; since children don't bother cleaning themselves up if
    -- their parents are already dead, I don't think there's a race
    -- condition here.  However, if there are any children, then we can
    -- infer that we need to clean ourselves up, so we do.
    -- finalCleanup = do
    --   cs <- readIORef $ _weakBag_children subs
    --   when (not $ IntMap.null cs) (cleanupRootSubscribed subscribed)
     -- writeIORef weakSelf =<< evaluate =<< mkWeakPtr subscribed (Just finalCleanup)
    returnSubscription (WeakBag.remove sln >> touch sln) zeroRef subscribedRef
      . coerce . DMap.lookup k
      =<< readIORef occRef

--------------------------------------------------------------------------------
-- Reflex integration
--------------------------------------------------------------------------------

-- | Designates the default, global Spider timeline
data SpiderTimeline x
type role SpiderTimeline nominal

-- | The default, global Spider environment
type Spider = SpiderTimeline Global

-- INFO: You'll be executing this at an event occurrence time, so
-- you're safe to use a simple pull-based read of the behavior?
instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (EventM x) where
  {-# INLINABLE sample #-}
  sample b = fixmeUnifySample (R.sample b) --TODO: Specialize sample to the Nothing and Just cases

makeLazyVal :: MonadIO m => m a -> IO (m a)
makeLazyVal get = do
  fmap (join . liftIO . readIORef) . mfix $ \ref ->
    newIORef $ do
      a <- get
      liftIO $ writeIORef ref $ pure a
      pure a

fixmeUnifySample :: Defer (SomeInit x) m => BehaviorM x b -> m b
fixmeUnifySample readV0 = liftIO . runBehaviorM readV0 Nothing =<< getDeferralQueue

unsafeBuildIncremental :: forall x p. (HasSpiderTimeline x, Patch p) => BehaviorM x (PatchTarget p) -> Event x p -> R.Incremental (SpiderTimeline x) p
unsafeBuildIncremental readV0 v' =
  -- TODO: using buildIncremental is lazier than the original implementation
  unsafePerformIO . runEventM @x $ buildIncremental (fixmeUnifySample readV0) $ v'
  -- TODO: why can't we do this? QueryT tests fail but others are fine (although they might not use unsafeBuild):
  -- SpiderIncremental $ Dynamic (Behavior readV0) v'

{-# INLINE buildIncremental #-}
-- Note: cannot examine its event until after the phase is over
buildIncremental :: forall x p m. (HasSpiderTimeline x, Patch p, Defer (SomeInit x) m)
  => EventM x (PatchTarget p) -> Event x p -> m (R.Incremental (SpiderTimeline x) p)
buildIncremental readV0 v' = do
  invsRef <- liftIO $ newIORef [] -- invalidators
  parentRef <- liftIO $ newIORef Nothing
  forceLazyHold <- liftIO $ makeLazyVal $ do
    valRef <- liftIO . newIORef =<< readV0
    defer $ SomeInit $ do
      maybeParent <- liftIO $ readIORef parentRef
      when (isNothing maybeParent) $ do
            liftIO . writeIORef parentRef . Just
              <=< subscribeWith v' (\a -> do
                                      v <- liftIO $ readIORef valRef
                                      forM_ (apply a v) $ \v'1 -> do
                                        vRef <- pure $! valRef
                                        iRef <- pure $! invsRef
                                        defer $ SomeAssignment @x vRef iRef v'1)
              $ Subscriber { subscriberPropagate = const (pure ())
                           , subscriberInvalidateHeight = \_ -> return ()
                           , subscriberRecalculateHeight = \_ -> return ()
                           }
    pure valRef
  defer $ SomeInit @x $ void $ forceLazyHold
  pure $ Incremental
    { incrementalCurrent = Behavior $ do
                  valRef <- liftIO (runEventM forceLazyHold)
                  addParentBAndInvalidator (BehaviorSubscribedHold parentRef) invsRef
--                  liftIO $ touch parentRef -- Otherwise, if this gets inlined enough, the hold's parent reference may get collected -- TODO: still needed?
                  liftIO $ readIORef valRef
    , incrementalPatches = v'
    }

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (EventM x) where
  {-# INLINABLE hold #-}
  hold v0 = fmap R.current . R.holdDyn v0
  {-# INLINABLE holdDyn #-}
  holdDyn v0 e = fmap SpiderDynamic . R.holdIncremental v0 $ coerce e
  {-# INLINABLE holdIncremental #-}
  holdIncremental v0 = buildIncremental (pure v0)
  {-# INLINABLE buildDynamic #-}
  buildDynamic readV0 = fmap SpiderDynamic . buildIncremental readV0 . coerce
  {-# INLINABLE headE #-}
  headE = R.slowHeadE
  {-# INLINABLE now #-}
  now = do
    nowOrNot <- liftIO $ newIORef $ Just ()
    defer $ Clear $ writeIORef nowOrNot Nothing
    return . Event $ \_ -> do
      occ <- liftIO . readIORef $ nowOrNot
      returnSubscription (pure ()) zeroRef () occ

-- INFO: With PullM you have to use readBehaviorTracked for Behavior's
-- change update mechanism?
instance Reflex.Class.MonadSample (SpiderTimeline x) (BehaviorM x) where
  {-# INLINABLE sample #-}
  sample = readBehaviorTracked

-- TODO: why not define Monad etc. on Dynamic in Reflex.Class?
instance HasSpiderTimeline x => Monad (Reflex.Class.Dynamic (SpiderTimeline x)) where
  {-# INLINE (>>=) #-}
  x >>= f =
    let d = fmap f x
    in R.unsafeBuildDynamic (R.sample (R.current =<< R.current d)) -- FIXME: Originally the following, why? (R.sample . R.current =<< R.sample (R.current d))
       . R.leftmost
       $ [ R.coincidence $ R.updated <$> R.updated d -- both
         , R.push (fmap Just . R.sample . R.current) $ R.updated d -- outer
         , R.switch $ R.updated <$> R.current d -- eInner
         ]
  {-# INLINE (>>) #-}
  (>>) = (*>)

instance HasSpiderTimeline x => Functor (Reflex.Class.Dynamic (SpiderTimeline x)) where
  {-# INLINE fmap #-}
  fmap f d = R.unsafeBuildDynamic (fmap f $ R.sample $ R.current d) (f <$> R.updated d)
  x <$ d = R.unsafeBuildDynamic (return x) $ x <$ R.updated d

instance HasSpiderTimeline x => Applicative (Reflex.Class.Dynamic (SpiderTimeline x)) where
  pure = SpiderDynamic . dynamicConst
  liftA2 = R.zipDynWith
  a <*> b = R.zipDynWith ($) a b
  a *> b = R.unsafeBuildDynamic (R.sample $ R.current b) $ R.leftmost [R.updated b, R.tag (R.current b) $ R.updated a]
  (<*) = flip (*>) -- There are no effects, so order doesn't matter

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE hold #-}
  hold v0 e = runFrame . runSpiderHostFrame $ Reflex.Class.hold v0 e
  {-# INLINABLE holdDyn #-}
  holdDyn v0 e = runFrame . runSpiderHostFrame $ Reflex.Class.holdDyn v0 e
  {-# INLINABLE holdIncremental #-}
  holdIncremental v0 e = runFrame . runSpiderHostFrame $ Reflex.Class.holdIncremental v0 e
  {-# INLINABLE buildDynamic #-}
  buildDynamic getV0 e = runFrame . runSpiderHostFrame $ Reflex.Class.buildDynamic getV0 e
  {-# INLINABLE headE #-}
  headE e = runFrame . runSpiderHostFrame $ Reflex.Class.headE e
  {-# INLINABLE now #-}
  now = runFrame . runSpiderHostFrame $ Reflex.Class.now
  

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (SpiderHostFrame x) where
  sample = SpiderHostFrame . R.sample

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (SpiderHostFrame x) where
  {-# INLINABLE hold #-}
  hold v0 e = SpiderHostFrame $ R.hold v0 e
  {-# INLINABLE holdDyn #-}
  holdDyn v0 e = SpiderHostFrame $ R.holdDyn v0 e
  {-# INLINABLE holdIncremental #-}
  holdIncremental v0 e = SpiderHostFrame $ R.holdIncremental v0 e
  {-# INLINABLE buildDynamic #-}
  buildDynamic getV0 e = SpiderHostFrame $ R.buildDynamic getV0 e
  {-# INLINABLE headE #-}
  headE = R.slowHeadE
  {-# INLINABLE now #-}
  now = SpiderHostFrame R.now

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE sample #-}
  sample = runFrame . R.sample

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  {-# INLINABLE sample #-}
  sample = Reflex.Spider.Internal.ReadPhase . Reflex.Class.sample

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  {-# INLINABLE hold #-}
  hold v0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.hold v0 e
  {-# INLINABLE holdDyn #-}
  holdDyn v0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.holdDyn v0 e
  {-# INLINABLE holdIncremental #-}
  holdIncremental v0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.holdIncremental v0 e
  {-# INLINABLE buildDynamic #-}
  buildDynamic getV0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.buildDynamic getV0 e
  {-# INLINABLE headE #-}
  headE e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.headE e
  {-# INLINABLE now #-}
  now = Reflex.Spider.Internal.ReadPhase Reflex.Class.now

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHostFrame x) where
  {-# INLINABLE subscribeEvent #-}
  subscribeEvent e = SpiderHostFrame $ do
    --TODO: Unsubscribe eventually (manually and/or with weak ref)
    valRef <- liftIO $ newIORef Nothing
    subscription <- subscribe e $ Subscriber
      { subscriberPropagate = writeAndScheduleClear valRef
      , subscriberInvalidateHeight = \_ -> return ()
      , subscriberRecalculateHeight = \_ -> return ()
      }
    return $ SpiderEventHandle
      { spiderEventHandleSubscription = subscription
      , spiderEventHandleValue = valRef
      }

instance HasSpiderTimeline x => Reflex.Host.Class.ReflexHost (SpiderTimeline x) where
  type EventTrigger (SpiderTimeline x) = RootTrigger x
  type EventHandle (SpiderTimeline x) = SpiderEventHandle x
  type HostFrame (SpiderTimeline x) = SpiderHostFrame x

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReadEvent (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  {-# NOINLINE readEvent #-}
  readEvent h = Reflex.Spider.Internal.ReadPhase $ fmap (fmap return) $ liftIO $ do
    result <- readIORef $ spiderEventHandleValue h
    touch h
    return result

instance Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHost x) where
  newEventWithTrigger = SpiderHost . newEventWithTriggerIO
  newFanEventWithTrigger f = SpiderHost $ do
    es <- newFanEventWithTriggerIO f
    return $ Reflex.Class.EventSelector $ select es

instance Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHostFrame x) where
  newEventWithTrigger = SpiderHostFrame . EventM . liftIO . newEventWithTriggerIO
  newFanEventWithTrigger f = SpiderHostFrame $ EventM $ liftIO $ do
    es <- newFanEventWithTriggerIO f
    return $ Reflex.Class.EventSelector $ select es

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE subscribeEvent #-}
  subscribeEvent = runFrame . runSpiderHostFrame . Reflex.Host.Class.subscribeEvent

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexHost (SpiderTimeline x) (SpiderHost x) where
  type ReadPhase (SpiderHost x) = Reflex.Spider.Internal.ReadPhase x
  fireEventsAndRead es (Reflex.Spider.Internal.ReadPhase a) = run es a
  runHostFrame = runFrame . runSpiderHostFrame

instance HasSpiderTimeline x => R.Reflex (SpiderTimeline x) where
  {-# SPECIALIZE instance R.Reflex (SpiderTimeline Global) #-}
  newtype Behavior (SpiderTimeline x) a = Behavior { readBehaviorTracked :: BehaviorM x a }
  newtype Event (SpiderTimeline x) a = Event { subscribeAndRead :: Subscriber x a -> EventM x (EventSubscription x, Maybe a) }
  data Incremental (SpiderTimeline x) p = Incremental { incrementalCurrent :: !(Behavior x (PatchTarget p))
                                                      , incrementalPatches :: Event x p -- This must be lazy; see the comment on buildIncremental
                                                      }
  newtype Dynamic (SpiderTimeline x) a = SpiderDynamic { unSpiderDynamic :: R.Incremental (SpiderTimeline x) (Identity a) } -- deriving (Functor, Applicative, Monad)
  type PullM (SpiderTimeline x) = BehaviorM x
  type PushM (SpiderTimeline x) = EventM x
  {-# INLINABLE never #-}
  never = Event $ const $ returnSubscription (pure ()) zeroRef () Nothing
  {-# INLINABLE constant #-}
  constant = Behavior . pure
  {-# INLINE push #-}
  push f e = cacheEvent (R.pushCheap f e)
  {-# INLINE [1] pushCheap #-}
  pushCheap !f e = Event $ \sub -> do
    (subscription, occ) <- subscribeAndRead e $ sub
      { subscriberPropagate = \a -> do
          mb <- f a
          mapM_ (subscriberPropagate sub) mb
      }
    occ' <- join <$> mapM f occ
    return (subscription, occ')
  {-# INLINABLE pull #-}
  pull = pull
  {-# INLINABLE fanG #-}
  fanG e = R.EventSelectorG $ selectG (fanG e)
  {-# INLINABLE mergeG #-}
  mergeG nt = mergeG nt . dynamicConst
  {-# INLINABLE switch #-}
  switch = switch
  {-# INLINABLE coincidence #-}
  coincidence = coincidence
  {-# INLINABLE current #-}
  current = coerce #. incrementalCurrent .# unSpiderDynamic
  {-# INLINABLE updated #-}
  updated = coerce #. incrementalPatches .# unSpiderDynamic
  {-# INLINABLE unsafeBuildDynamic #-}
  unsafeBuildDynamic readV0 v' = SpiderDynamic $ R.unsafeBuildIncremental readV0 $ fmap Identity v'
  {-# INLINABLE unsafeBuildIncremental #-}
  unsafeBuildIncremental = unsafeBuildIncremental
  {-# INLINABLE mergeIncrementalG #-}
  mergeIncrementalG nt = mergeG nt
  {-# INLINABLE mergeIncrementalWithMoveG #-}
  mergeIncrementalWithMoveG nt = mergeWithMove nt
  {-# INLINABLE currentIncremental #-}
  currentIncremental = incrementalCurrent
  {-# INLINABLE updatedIncremental #-}
  updatedIncremental = incrementalPatches
  {-# INLINABLE incrementalToDynamic #-}
  incrementalToDynamic i =
    let currentI = R.currentIncremental i
    in R.unsafeBuildDynamic (R.sample currentI)
       $ R.push (\p -> fmap (apply p) (R.sample currentI)) --TODO: Avoid the redundant 'apply'
       $ R.updatedIncremental i
  eventCoercion Coercion = Coercion
  behaviorCoercion Coercion = Coercion
  dynamicCoercion = unsafeCoerce -- FIXME
  incrementalCoercion Coercion = unsafeCoerce -- FIXME
  {-# INLINABLE mergeIntIncremental #-}
  mergeIntIncremental = mergeInt . coerce
  {-# INLINABLE fanInt #-}
  fanInt e = R.EventSelectorInt $ selectInt (fanInt e)

instance MonadRef (EventM x) where
  type Ref (EventM x) = Ref IO
  {-# INLINABLE newRef #-}
  {-# INLINABLE readRef #-}
  {-# INLINABLE writeRef #-}
  newRef = liftIO . newRef
  readRef = liftIO . readRef
  writeRef r a = liftIO $ writeRef r a

instance MonadAtomicRef (EventM x) where
  {-# INLINABLE atomicModifyRef #-}
  atomicModifyRef r f = liftIO $ atomicModifyRef r f

instance MonadFail (SpiderHost x) where
  {-# INLINABLE fail #-}
  fail s = SpiderHost $ MonadFail.fail s

-- | Run an action affecting the global Spider timeline; this will be guarded by
-- a mutex for that timeline
runSpiderHost :: SpiderHost Global a -> IO a
runSpiderHost (SpiderHost a) = a

-- | Run an action affecting a given Spider timeline; this will be guarded by a
-- mutex for that timeline
runSpiderHostForTimeline :: SpiderHost x a -> SpiderTimelineEnv x -> IO a
runSpiderHostForTimeline (SpiderHost a) _ = a

newtype SpiderHostFrame (x :: Type) a = SpiderHostFrame { runSpiderHostFrame :: EventM x a }
  deriving (Functor, Applicative, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadMask, MonadThrow, MonadCatch)

instance Monad (SpiderHostFrame x) where
  {-# INLINABLE (>>=) #-}
  SpiderHostFrame x >>= f = SpiderHostFrame $ x >>= runSpiderHostFrame . f

instance NotReady (SpiderTimeline x) (SpiderHostFrame x) where
  notReadyUntil _ = pure ()
  notReady = pure ()

newEventWithTriggerIO :: forall x a. (RootTrigger x a -> IO (IO ())) -> IO (Event x a)
newEventWithTriggerIO f = do
  es <- newFanEventWithTriggerIO $ \Refl -> f
  return $ select es Refl

newtype ReadPhase x a = ReadPhase (EventM x a) deriving (Functor, Applicative, Monad, MonadFix)

instance MonadRef (SpiderHost x) where
  type Ref (SpiderHost x) = Ref IO
  newRef = SpiderHost . newRef
  readRef = SpiderHost . readRef
  writeRef r = SpiderHost . writeRef r

instance MonadAtomicRef (SpiderHost x) where
  atomicModifyRef r = SpiderHost . atomicModifyRef r

instance MonadRef (SpiderHostFrame x) where
  type Ref (SpiderHostFrame x) = Ref IO
  newRef = SpiderHostFrame . newRef
  readRef = SpiderHostFrame . readRef
  writeRef r = SpiderHostFrame . writeRef r

instance MonadAtomicRef (SpiderHostFrame x) where
  atomicModifyRef r = SpiderHostFrame . atomicModifyRef r

instance PrimMonad (SpiderHostFrame x) where
  type PrimState (SpiderHostFrame x) = PrimState IO
  primitive = SpiderHostFrame . EventM . primitive

instance NotReady (SpiderTimeline x) (SpiderHost x) where
  notReadyUntil _ = return ()
  notReady = return ()

instance HasSpiderTimeline x => NotReady (SpiderTimeline x) (PerformEventT (SpiderTimeline x) (SpiderHost x)) where
  notReadyUntil _ = return ()
  notReady = return ()
