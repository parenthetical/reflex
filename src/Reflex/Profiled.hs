{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
-- |
-- Module:
--   Reflex.Profiled
-- Description:
--   This module contains an instance of the 'Reflex' class that provides
--   profiling/cost-center information.
module Reflex.Profiled where

import Control.Monad
import Control.Monad.Exception
import Control.Monad.Fix
import Control.Monad.Primitive
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State.Strict (StateT, execStateT, modify)
import Data.Bifunctor
import Data.Coerce
import Data.Dependent.Map (DMap)
import Data.GADT.Compare (GCompare)
import Data.FastMutableIntMap
import Data.IORef
import Data.List
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid ((<>))
import Data.Ord
import Data.Profunctor.Unsafe ((#.))
import qualified Data.Semigroup as S
import Data.Type.Coercion
import Foreign.Ptr
import GHC.Foreign
import GHC.IO.Encoding
import GHC.Stack
import Reflex.Adjustable.Class
import Reflex.BehaviorWriter.Class
import Reflex.Class
import Reflex.DynamicWriter.Class
import Reflex.EventWriter.Class
import Reflex.Host.Class
import Reflex.NotReady.Class
import Reflex.PerformEvent.Class
import Reflex.PostBuild.Class
import Reflex.Query.Class
import Reflex.Requester.Class
import Reflex.TriggerEvent.Class

import System.IO.Unsafe
import Unsafe.Coerce (unsafeCoerce)

data ProfiledTimeline t

{-# NOINLINE profilingData #-}
profilingData :: IORef (Map (Ptr CostCentreStack) Int)
profilingData = unsafePerformIO $ newIORef Map.empty

data CostCentreTree = CostCentreTree
  { _costCentreTree_ownEntries :: !Int
  , _costCentreTree_cumulativeEntries :: !Int
  , _costCentreTree_children :: !(Map (Ptr CostCentre) CostCentreTree)
  }
  deriving (Show, Eq, Ord)

instance S.Semigroup CostCentreTree where
  (CostCentreTree oa ea ca) <> (CostCentreTree ob eb cb) =
      CostCentreTree (oa + ob) (ea + eb) $ Map.unionWith (S.<>) ca cb

instance Monoid CostCentreTree where
  mempty = CostCentreTree 0 0 mempty
  mappend = (S.<>)

getCostCentreStack :: Ptr CostCentreStack -> IO [Ptr CostCentre]
getCostCentreStack = go []
  where go l ccs = if ccs == nullPtr
          then return l
          else do
          cc <- ccsCC ccs
          parent <- ccsParent ccs
          go (cc : l) parent

toCostCentreTree :: Ptr CostCentreStack -> Int -> IO CostCentreTree
toCostCentreTree ccs n =
  foldr (\cc child -> CostCentreTree 0 n $ Map.singleton cc child) (CostCentreTree n n mempty)
    <$> getCostCentreStack ccs

getCostCentreTree :: IO CostCentreTree
getCostCentreTree = do
  vals <- readIORef profilingData
  mconcat <$> mapM (uncurry toCostCentreTree) (Map.toList vals)

formatCostCentreTree :: CostCentreTree -> IO String
formatCostCentreTree cct0 = unlines . reverse <$> execStateT (go 0 cct0) []
  where go :: Int -> CostCentreTree -> StateT [String] IO ()
        go depth cct = do
          let children = sortOn (Down . _costCentreTree_cumulativeEntries . snd) $ Map.toList $ _costCentreTree_children cct
              indent = mconcat $ replicate depth "  "
          forM_ children $ \(cc, childCct) -> do
            lbl <- liftIO $ peekCString utf8 =<< ccLabel cc
            mdl <- liftIO $ peekCString utf8 =<< ccModule cc
            loc <- liftIO $ peekCString utf8 =<< ccSrcSpan cc
            let description = mdl <> "." <> lbl <> " (" <> loc <> ")"
            modify $ (:) $ indent <> description <> "\t" <> show (_costCentreTree_cumulativeEntries childCct) <> "\t" <> show (_costCentreTree_ownEntries childCct)
            go (succ depth) childCct

showProfilingData :: IO ()
showProfilingData = do
  putStr =<< formatCostCentreTree =<< getCostCentreTree

writeProfilingData :: FilePath -> IO ()
writeProfilingData p = do
  writeFile p =<< formatCostCentreTree =<< getCostCentreTree

newtype ProfiledM m a = ProfiledM { runProfiledM :: m a }
  deriving (Functor, Applicative, Monad, MonadFix, MonadException, MonadAsyncException)

profileEvent :: Reflex t => Event t a -> Event t a
profileEvent e = unsafePerformIO $ do
  stack <- getCurrentCCS e
  let f x = unsafePerformIO $ do
        modifyIORef' profilingData $ Map.insertWith (+) stack 1
        return $ return $ Just x
  return $ pushCheap f e

--TODO: Instead of profiling just the input or output of each one, profile all the inputs and all the outputs

deriving instance (Reflex t) => Functor (Behavior (ProfiledTimeline t))
deriving instance (Reflex t) => Applicative (Behavior (ProfiledTimeline t))
deriving instance (Reflex t) => Monad (Behavior (ProfiledTimeline t))
deriving instance (Reflex t) => MonadFix (Behavior (ProfiledTimeline t))

instance Reflex t => Reflex (ProfiledTimeline t) where
  newtype Behavior (ProfiledTimeline t) a = Behavior_Profiled { unBehavior_Profiled :: Behavior t a }
  newtype Event (ProfiledTimeline t) a = Event_Profiled { unEvent_Profiled :: Event t a }
  type PushM (ProfiledTimeline t) = ProfiledM (PushM t)
  never = Event_Profiled never
  cacheEvent (Event_Profiled e) = Event_Profiled (cacheEvent e)
  pushCheap f (Event_Profiled e) = coerce $ pushCheap (coerce f) $ profileEvent e
  fanG (Event_Profiled e) = EventSelectorG $ coerce $ selectG (fanG $ profileEvent e)
  switchUncached (Behavior_Profiled b) = coerce $ profileEvent $ switchUncached (coerceBehavior b)
  coincidenceUncached (Event_Profiled e) = coerce $ profileEvent $ coincidenceUncached (coerceEvent e)
  mergeListUncached = Event_Profiled . mergeListUncached . fmap unEvent_Profiled
  behaviorCoercion c =
    Coercion `trans` behaviorCoercion @t c `trans` Coercion
  eventCoercion c =
    Coercion `trans` eventCoercion @t c `trans` Coercion
  fanInt (Event_Profiled e) = coerce $ fanInt $ profileEvent e

instance MonadHold t m => MonadHold (ProfiledTimeline t) (ProfiledM m) where
  liftPush (ProfiledM m) = ProfiledM $ liftPush m
  hold v0 (Event_Profiled v') = ProfiledM $ Behavior_Profiled <$> hold v0 v'
  now = ProfiledM $ Event_Profiled <$> now

instance MonadSample t m => MonadSample (ProfiledTimeline t) (ProfiledM m) where
  sample (Behavior_Profiled b) = ProfiledM $ sample b

instance Adjustable t m => Adjustable (ProfiledTimeline t) (ProfiledM m) where
  runWithReplace a0 a' = (fmap . fmap) coerce . lift $
    runWithReplace (coerce a0) (coerce $ coerce <$> a')
  traverseIntMapWithKeyWithAdjust f dm0 dm' = (fmap . fmap) coerce . lift $
    traverseIntMapWithKeyWithAdjust (\k v -> coerce $ f k v) dm0 (coerce dm')
  traverseDMapWithKeyWithAdjust f dm0 dm' = (fmap . fmap) coerce . lift $
    traverseDMapWithKeyWithAdjust (\k v -> coerce $ f k v) dm0 (coerce dm')
  traverseDMapWithKeyWithAdjustWithMove f dm0 dm' = (fmap . fmap) coerce . lift $
    traverseDMapWithKeyWithAdjustWithMove (\k v -> coerce $ f k v) dm0 (coerce dm')

instance MonadTrans ProfiledM where
  lift = ProfiledM

instance MonadIO m => MonadIO (ProfiledM m) where
  liftIO = lift . liftIO

instance PerformEvent t m => PerformEvent (ProfiledTimeline t) (ProfiledM m) where
  type Performable (ProfiledM m) = Performable m
  performEvent_ = lift . performEvent_ . coerce
  performEvent = lift . fmap coerce . performEvent . coerce

instance TriggerEvent t m => TriggerEvent (ProfiledTimeline t) (ProfiledM m) where
  newTriggerEvent = first coerce <$> lift newTriggerEvent
  newTriggerEventWithOnComplete = first coerce <$> lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete f = coerce <$> lift (newEventWithLazyTriggerWithOnComplete f)

instance PostBuild t m => PostBuild (ProfiledTimeline t) (ProfiledM m) where
  getPostBuild = coerce <$> lift getPostBuild

instance NotReady t m => NotReady (ProfiledTimeline t) (ProfiledM m) where
  notReady = lift notReady
  notReadyUntil = lift . notReadyUntil . coerce

instance BehaviorWriter t w m => BehaviorWriter (ProfiledTimeline t) w (ProfiledM m) where
  tellBehavior = lift . tellBehavior . coerce

instance DynamicWriter t w m => DynamicWriter (ProfiledTimeline t) w (ProfiledM m) where
  tellDyn = lift . tellDyn . unsafeCoerce

instance EventWriter t w m => EventWriter (ProfiledTimeline t) w (ProfiledM m) where
  tellEvent = lift . tellEvent . unsafeCoerce

instance MonadQuery t q m => MonadQuery (ProfiledTimeline t) q (ProfiledM m) where
  tellQueryIncremental = lift . tellQueryIncremental . unsafeCoerce
  askQueryResult = unsafeCoerce <$> lift askQueryResult
  queryIncremental = fmap unsafeCoerce . lift . queryIncremental . unsafeCoerce

instance Requester t m => Requester (ProfiledTimeline t) (ProfiledM m) where
  type Request (ProfiledM m) = Request m
  type Response (ProfiledM m) = Response m

  requesting = fmap coerce . lift . requesting . coerce
  requesting_ = lift . requesting_ . coerce

instance MonadRef m => MonadRef (ProfiledM m) where
  type Ref (ProfiledM m) = Ref m
  newRef = lift . newRef
  readRef = lift . readRef
  writeRef r = lift . writeRef r

instance MonadReflexCreateTrigger t m => MonadReflexCreateTrigger (ProfiledTimeline t) (ProfiledM m) where
  newEventWithTrigger = lift . fmap coerce . newEventWithTrigger
  newFanEventWithTrigger f = do
    es <- lift $ newFanEventWithTrigger f
    return $ EventSelector $ \k -> coerce $ select es k

instance MonadReader r m => MonadReader r (ProfiledM m) where
  ask = lift ask
  local f (ProfiledM a) = ProfiledM $ local f a
  reader = lift . reader

instance ReflexHost t => ReflexHost (ProfiledTimeline t) where
  type EventTrigger (ProfiledTimeline t) = EventTrigger t
  type EventHandle (ProfiledTimeline t) = EventHandle t
  type HostFrame (ProfiledTimeline t) = ProfiledM (HostFrame t)

instance MonadSubscribeEvent t m => MonadSubscribeEvent (ProfiledTimeline t) (ProfiledM m) where
  subscribeEvent = lift . subscribeEvent . coerce

instance PrimMonad m => PrimMonad (ProfiledM m) where
  type PrimState (ProfiledM m) = PrimState m
  primitive = lift . primitive

instance MonadReflexHost t m => MonadReflexHost (ProfiledTimeline t) (ProfiledM m) where
  type ReadPhase (ProfiledM m) = ProfiledM (ReadPhase m)
  fireEventsAndRead ts r = lift $ fireEventsAndRead ts $ coerce r
  runHostFrame = lift . runHostFrame . coerce

instance MonadReadEvent t m => MonadReadEvent (ProfiledTimeline t) (ProfiledM m) where
  readEvent = lift . fmap coerce . readEvent
