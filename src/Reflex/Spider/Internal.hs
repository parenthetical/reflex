{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}
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
{-# LANGUAGE PatternSynonyms #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
{-# OPTIONS_GHC -Wunused-binds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module is the implementation of the 'Spider' 'Reflex' engine.  It uses
-- a graph traversal algorithm to propagate 'Event's and 'Behavior's.
module Reflex.Spider.Internal
  ( pattern Event,
    subscribeAndRead,
    SpiderHostFrame(SpiderHostFrame),
    SpiderTimeline,
    Global,
    Subscriber(subscriberPropagate),
    runSpiderHost,
    Spider,
    SpiderHost,
    runSpiderHostForTimeline,
    newSpiderTimeline,
    withSpiderTimeline ) where

import Control.Monad hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Identity hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Ref
import Data.Foldable hiding (concat, elem, sequence_)
import Data.Maybe hiding (mapMaybe)
import GHC.Exts hiding (toList)
import Data.Type.Coercion
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
import Data.GADT.Compare
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
import Control.Monad.Reader
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Text.Printf (printf)
-- import Debug.RecoverRTTI (anythingToString)

anythingToString :: p -> String
anythingToString _ = "<anythingToString>"

{-# NOINLINE nodeCtrRef #-}
nodeCtrRef :: IORef Int
nodeCtrRef = unsafePerformIO $ newIORef (0 :: Int)

newNodeId :: (MonadIO m) => m Int
newNodeId = liftIO $ atomicModifyIORef nodeCtrRef (\n -> (succ n, n))

--NB: Once you subscribe to an Event, you must always hold on the the WHOLE EventSubscription you get back
-- If you do not retain the subscription, you may be prematurely unsubscribed from the parent event.
data EventSubscription x = EventSubscription
  { unsubscribe :: !(IO ())
  , _eventSubscription_subscribed :: {-# UNPACK #-} !Any
  }

newtype Subscriber x a = Subscriber
  { subscriberPropagate :: Maybe a -> EventM x ()
  }

-- Why do we use Any here, instead of just using an
-- existential type? Sadly, GHC does not currently know how to unbox types
-- with existentially quantified fields. So instead we just coerce values
-- to type Any on the way in. Since we never coerce them back, this is
-- perfectly safe.
returnSubscription :: Monad m => IO () -> a -> b -> m (EventSubscription x, b)
returnSubscription cleanup retained occ =
  return (EventSubscription cleanup (toAny retained), occ)

subscribeWithRec :: R.Event (SpiderTimeline x) a -> (EventSubscription x -> Maybe a -> EventM x (Maybe b)) -> Subscriber x b -> EventM x (EventSubscription x, Maybe (Maybe b))
subscribeWithRec e f subscriber = mdo
  (subscription, occ) <- subscribeAndRead e $ subscriber
         { subscriberPropagate = \mocc -> do
             subscriberPropagate subscriber <=< (subscription `f`) $ mocc
         }
  occ' <- mapM (subscription `f`) occ
  return (subscription, occ')


-- | Propagate everything
propagate :: forall x a. Maybe a -> WeakBag (Subscriber x a) -> EventM x ()
propagate a subscribers =
  -- Note: in the following traversal, we do not visit nodes that are added to the list during our traversal; they are new events, which will necessarily have full information already, so there is no need to traverse them
  --TODO: Should we check if nodes already have their values before propagating?  Maybe we're re-doing work
  WeakBag.traverse_ subscribers $ \s -> subscriberPropagate s a

toAny :: a -> Any
toAny = unsafeCoerce

-- | Stores all global data relevant to a particular Spider timeline; only one
-- value should exist for each type @x@
newtype SpiderTimelineEnv (x :: Type) = STE {unSTE :: SpiderTimelineEnv' x}
-- We implement SpiderTimelineEnv with a newtype wrapper so
-- we can get the coercions we want safely.

data SpiderTimelineEnv' x = SpiderTimelineEnv
  { _spiderTimeline_lock :: {-# UNPACK #-} !(MVar ())
  , _spiderTimeline_eventEnv :: {-# UNPACK #-} !(EventEnv x)
  , _spiderTimeline_rootTriggers :: {-# UNPACK #-} !(IORef (IntMap (Some (RootTrigger x))))
  , _spiderTimeline_never :: {-# UNPACK #-} !(Subscriber x () -> EventM x (EventSubscription x, Maybe (Maybe ()))) -- R.Event (SpiderTimeline x) ()
  }

data EventEnv x
   = EventEnv { eventEnvAssignments :: !(IORef [SomeAssignment x]) -- Needed for Subscribe  -- This should only actually get used when events are firing
              , eventEnvInits :: !(IORef [EventM x ()]) -- Needed for Subscribe
              , eventEnvClears :: !(IORef [Clear]) -- Needed for Subscribe
              , eventEnvUnsubscribes :: !(IORef [EventSubscription x])
              , eventEnvBla :: !(IORef [IO (EventSubscription x)])
              }
   
asksEventEnv :: forall x a. HasSpiderTimeline x => (EventEnv x -> a) -> EventM x a
asksEventEnv f = return $ f $ _spiderTimeline_eventEnv (unSTE (spiderTimeline :: SpiderTimelineEnv x))

addToQueue :: MonadIO m => a -> IORef [a] -> m ()
addToQueue (!a) q = liftIO $ modifyIORef' q (a:)

deferClear :: forall x. HasSpiderTimeline x => IO () -> EventM x ()
deferClear thunk = addToQueue (Clear thunk) =<< asksEventEnv eventEnvClears

deferUnsubscribe :: HasSpiderTimeline x => EventSubscription x -> EventM x ()
deferUnsubscribe subscription = addToQueue subscription =<< asksEventEnv eventEnvUnsubscribes

deferBla :: HasSpiderTimeline x => IO (EventSubscription x) -> EventM x ()
deferBla x = addToQueue x =<< asksEventEnv eventEnvBla

{-# INLINE writeAndScheduleClear #-}
writeAndScheduleClear :: forall x a. HasSpiderTimeline x => String -> IORef (Maybe a) -> a -> EventM x ()
writeAndScheduleClear info ref val = do
  prevVal <- liftIO $ readIORef ref
  when (isJust prevVal) $ error $ "Val was already set in " <> info <> ". Old:" <> anythingToString (fromJust prevVal) <> ", new: " <> anythingToString val
  liftIO $ writeIORef ref (Just val)
  deferClear $ writeIORef ref Nothing

-- EventM can do everything BehaviorM can, plus create holds
newtype EventM x a = EventM { runEventM :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadException, MonadAsyncException, MonadCatch, MonadThrow, MonadMask)

-- Propagate the given event occurrence; before cleaning up, run the given action, which may read the state of events and behaviors
run :: forall x b. HasSpiderTimeline x => [DSum (RootTrigger x) Identity] -> EventM x b -> SpiderHost x b
run roots after = do
  let t = spiderTimeline :: SpiderTimelineEnv x
  liftIO $ putStrLn "\nRUN ~~~"
  SpiderHost $ withMVar (_spiderTimeline_lock (unSTE t)) $ \_ -> unSpiderHost $ runFrame $ do
    rootsToPropagate <- forM roots $ \r@(RootTrigger (_triggerId, _, occRef, k) :=> a) -> do
      occBefore <- liftIO $ readIORef occRef
      liftIO $ writeIORef occRef $! Just $ DMap.insert k a (fromMaybe mempty occBefore)
      if isNothing occBefore
        then do deferClear $ writeIORef occRef Nothing
                return $ Just r
        else return Nothing
    forM_ (catMaybes rootsToPropagate) $ \(RootTrigger (triggerId, subscribersRef, _, _) :=> Identity a) -> do
      liftIO $ printf "Propagating trigger %d with value %s\n" triggerId $ anythingToString a
      propagate (Just a) subscribersRef
    triggers <- liftIO $ readIORef $ _spiderTimeline_rootTriggers (unSTE (spiderTimeline :: SpiderTimelineEnv x))
    forM_ triggers $ \(Some (RootTrigger (triggerId, subscribersRef, occRef, _))) -> do
      occ <- liftIO $ readIORef occRef
      when (isNothing occ) $ do
        liftIO $ writeIORef occRef (Just mempty)
        deferClear $ writeIORef occRef Nothing
        liftIO $ printf "Propagating null trigger %d\n" triggerId
        propagate Nothing subscribersRef
    after

newtype Clear = Clear (IO ())

data SomeAssignment x = forall a. SomeAssignment {-# UNPACK #-} !(IORef a) {-# UNPACK #-} !(IORef [Weak Invalidator]) a

invalidate :: IORef [Weak Invalidator] -> IO ()
invalidate wisRef = do
  mapM_ (\wi -> maybe (pure ()) (\i -> finalize wi >> i) <=< deRefWeak $ wi) =<< readIORef wisRef
  writeIORef wisRef []

-- | Run an event action outside of a frame
runFrame :: forall x a. HasSpiderTimeline x => EventM x a -> SpiderHost x a --TODO: This function also needs to hold the mutex
runFrame a = SpiderHost $ do
  liftIO $ putStrLn "-- START RUNFRAME"
  let (EventEnv toAssignRef initRef toClearRef toUnsubscribeRef toBlaRef) =
        _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  liftIO $ putStrLn ">>> Running inits"
  let env = _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  result <- runEventM $ do
        result <- a
        -- This must happen before doing the assignments, in case subscribing a Hold causes existing Holds to be read by the newly-propagated events:
        runHoldInits (eventEnvInits env)
        return result
  liftIO $ putStrLn "<<< End running inits"
  putStrLn "-- CLEARING"
  readIORef toClearRef >>= mapM_ (\(Clear m) -> m)
  writeIORef toClearRef []
  putStrLn "-- ASSIGNMENTS"
  readIORef toAssignRef >>= mapM_ (\(SomeAssignment vRef iRef v) -> do
                                      writeIORef vRef v
                                      invalidate iRef)
  writeIORef toAssignRef []
  ----------------
  toBla <- readIORef toBlaRef
  toUnsubscribe <- readIORef toUnsubscribeRef
  writeIORef toUnsubscribeRef []
  writeIORef initRef []
  writeIORef toBlaRef []
  putStrLn "-- BLA"
  toUnsubscribeBla <- sequence toBla
  putStrLn "-- UNSUBSCRIBING"
  mapM_ unsubscribe toUnsubscribe
  mapM_ unsubscribe toUnsubscribeBla
  putStrLn "-- DONE RUNFRAME"
  return result

runHoldInits :: MonadIO m => IORef [m a] -> m ()
runHoldInits initsRef = fix $ \runHoldInits' -> do
  inits <- liftIO $ readIORef initsRef
  unless (null inits) $ do
    liftIO $ writeIORef initsRef []
    sequence_ inits
    runHoldInits'

unsafeNewSpiderTimelineEnv :: forall x. IO (SpiderTimelineEnv x)
unsafeNewSpiderTimelineEnv = do
  lock <- newMVar ()
  env <- do toAssignRef <- newIORef []
            initRef <- newIORef []
            toClearRef <- newIORef []
            toUnsubscribeRef <- newIORef []
            toBlaRef <- newIORef []
            return $ EventEnv toAssignRef initRef toClearRef toUnsubscribeRef toBlaRef
  triggers <- newIORef mempty
  Event never' <- newEventWithTriggerIO' triggers (\_ -> pure (pure ()))
  return $ STE $ SpiderTimelineEnv
    { _spiderTimeline_lock = lock
    , _spiderTimeline_eventEnv = env
    , _spiderTimeline_rootTriggers = triggers
    , _spiderTimeline_never = never'
    }

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (EventM x) where
  {-# INLINABLE sample #-}
  sample b = liftIO . runBehaviorM (R.sample b) Nothing =<< asksEventEnv eventEnvInits

data BehaviorEnv x = BehaviorEnv
  { behaviorEnvMaybeWISubs :: Maybe (Weak Invalidator, IORef [BehaviorSubscribed x])
  , behaviorEnvInitsRef :: IORef [EventM x ()]
  }

-- BehaviorM can sample behaviors
newtype BehaviorM (x :: Type) a = BehaviorM { unBehaviorM :: ReaderIO (BehaviorEnv x) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadReader (BehaviorEnv x))

-- INFO: This seems to keep hold of all events which might influence a Behavior's value?
data BehaviorSubscribed x
   = BehaviorSubscribedHold !(IORef (EventSubscription x))
   | BehaviorSubscribedPull ![BehaviorSubscribed x]

type Invalidator = IO ()

runBehaviorM :: BehaviorM x a -> Maybe (Weak Invalidator, IORef [BehaviorSubscribed x]) -> IORef [EventM x ()] -> IO a
runBehaviorM a mwi holdInits = runReaderIO (unBehaviorM a) (BehaviorEnv mwi holdInits)

-- | Log an Event or Behavior which influences the value of this Behavior.
tellBehaviorParent :: BehaviorSubscribed x -> BehaviorM x ()
tellBehaviorParent h = do
  !m <- asks behaviorEnvMaybeWISubs
  forM_ m $ \(_, !p) -> liftIO $ modifyIORef' p (h :)

addThisBehaviorMsInvalidator :: IORef [Weak Invalidator] -> BehaviorM x ()
addThisBehaviorMsInvalidator invsRef = do
  !m <- asks behaviorEnvMaybeWISubs
  forM_ m $ \(!wi, _) -> liftIO $ modifyIORef' invsRef (wi:)

instance Reflex.Class.MonadSample (SpiderTimeline x) (BehaviorM x) where
  {-# INLINABLE sample #-}
  sample = readBehaviorTracked

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (EventM x) where
  {-# NOINLINE buildHold #-}
  -- Note: cannot examine its event until after the phase is over
  buildHold readV0 e = do
    liftIO $ putStrLn "buildHold running"
    !initsQueue <- asksEventEnv eventEnvInits
    invsRef <- liftIO $ newIORef [] -- invalidators
    parentRef <- liftIO $ newIORef $ error "buildHold: parentRef uninitialized"
    let forceLazyHoldReturnValRef = unsafePerformIO . runEventM @x $ do
          valRef <- liftIO . newIORef =<< readV0
          flip addToQueue initsQueue $! do
            liftIO . writeIORef parentRef . fst
                <=< subscribeWithRec e (\_ ma -> mapM (\a -> do
                                                          vRef <- pure $! valRef
                                                          iRef <- pure $! invsRef
                                                          liftIO $ printf "Hold update %s\n" $ anythingToString a
                                                          addToQueue (SomeAssignment @x vRef iRef a) =<< asksEventEnv eventEnvAssignments
                                                          pure a)
                                                 ma)
                $ Subscriber (const (pure ()))
          pure valRef
    flip addToQueue initsQueue $ void $ liftIO $ evaluate forceLazyHoldReturnValRef
    pure $ Behavior $ do
      tellBehaviorParent (BehaviorSubscribedHold parentRef)
      addThisBehaviorMsInvalidator invsRef
      liftIO $ readIORef forceLazyHoldReturnValRef
  {-# INLINABLE now #-}
  now = do
    nowOrNot <- liftIO $ newIORef $ Just ()
    deferClear $ writeIORef nowOrNot Nothing
    return . Event $ \sub -> do
      liftIO $ putStrLn "now being subscribed to"
      occ <- liftIO . readIORef $ nowOrNot
      (neverSubscription,_) <- subscribeAndRead R.never $ Subscriber $ \_ -> do
        occ' <- liftIO . readIORef $ nowOrNot
        when (isNothing occ') $ subscriberPropagate sub Nothing
      returnSubscription (unsubscribe neverSubscription) neverSubscription (Just occ)

instance HasSpiderTimeline x => R.Reflex (SpiderTimeline x) where
  {-# SPECIALIZE instance R.Reflex (SpiderTimeline Global) #-}
  newtype Behavior (SpiderTimeline x) a = Behavior { readBehaviorTracked :: BehaviorM x a }
  newtype Event (SpiderTimeline x) a = Event { subscribeAndRead :: Subscriber x a -> EventM x (EventSubscription x, Maybe (Maybe a)) }
  type PullM (SpiderTimeline x) = BehaviorM x
  type PushM (SpiderTimeline x) = EventM x
  {-# INLINABLE never #-}
  never = error "never value got evaluated??" <$ Event (_spiderTimeline_never (unSTE (spiderTimeline :: SpiderTimelineEnv x))) -- Event $ const $ returnSubscription (pure ()) () (Just Nothing)
  {-# NOINLINE [0] cacheEvent #-}
  cacheEvent :: forall a. R.Event (SpiderTimeline x) a -> R.Event (SpiderTimeline x) a
  cacheEvent e = unsafePerformIO $ do
    liftIO $ putStrLn "cacheEvent being subscribed to"
    subscribers :: WeakBag (Subscriber x a) <- WeakBag.empty
    parentSubscriptionRef :: IORef (EventSubscription x) <- newIORef $ error "cacheEvent: parentRef uninitialized"
    occRef :: IORef (Maybe (Maybe a)) <- newIORef Nothing
    pure $ Event $ \sub -> do
      do notSubscribed <- liftIO (WeakBag.null subscribers)
         when notSubscribed $
           liftIO . writeIORef parentSubscriptionRef . fst
           <=< subscribeWithRec e (\_ occ -> writeAndScheduleClear "cacheEvent" occRef occ >> pure occ)
           $ Subscriber { subscriberPropagate = flip propagate subscribers }
      parentSub <- liftIO $ readIORef parentSubscriptionRef
      sln <- liftIO $ WeakBag.insert' sub subscribers $ unsubscribe parentSub >> writeIORef parentSubscriptionRef (error "cacheEvent: parentRef uninitialized")
      returnSubscription (WeakBag.remove sln >> touch sln)
                         (sln, parentSubscriptionRef, subscribers)
                         <=< liftIO $ readIORef occRef
  {-# INLINE [1] pushCheap #-}
  pushCheap !f e = Event $ subscribeWithRec e (\_ -> fmap join . mapM f)
  {-# INLINABLE pull #-}
  pull a = unsafePerformIO $ do
    ref :: IORef (Maybe (a, [BehaviorSubscribed x])) <- newIORef Nothing
    invsRef :: IORef [Weak Invalidator] <- newIORef []
    pure $ Behavior $ do
      (val, parents) <- liftIO (readIORef ref) >>= maybe (do
                      let i = readIORef ref >>= mapM_ (const $ writeIORef ref Nothing >> invalidate invsRef)
                      wi <- liftIO $ mkWeakPtr i Nothing
                      parentsRef <- liftIO $ newIORef []
                      !holdInits <- BehaviorM $ asks behaviorEnvInitsRef
                      aVal <- liftIO $ runBehaviorM a (Just (wi, parentsRef)) holdInits
                      parents <- liftIO $ readIORef parentsRef
                      let subscribed = (aVal, parents)
                      liftIO $ writeIORef ref $ Just subscribed
                      return subscribed)
                    pure
      tellBehaviorParent (BehaviorSubscribedPull parents)
      addThisBehaviorMsInvalidator invsRef
      pure val
  switchUncached switchParent = Event $ \sub -> mdo
    parentsRef <- liftIO $ newIORef [] --TODO: This should be unnecessary, because it will always be filled with just the single parent behavior
    holdInitsRef <- asksEventEnv eventEnvInits
    subscriptionRef <- liftIO $ newIORef $ error "switchUncached: subscriptionRef uninitialized"
    wiRef <- liftIO $ newIORef $ error "switchUncached: wiRef uninitialized"
    let subscriber = Subscriber $  \ma -> do
          liftIO $ printf "Switch propagating update: %s\n" $ anythingToString ma
          subscriberPropagate sub ma
    -- TODO: holdInitsRef is always empty, parentsRef is always length 1?
    let f = do
          i <- liftIO $ evaluate switchInvalidator
          wi <- liftIO $ mkWeakPtr i Nothing
          liftIO $ writeIORef wiRef wi
          e <- liftIO $ runBehaviorM (R.sample switchParent) (Just (wi, parentsRef)) holdInitsRef
          (subscription, occ) <- subscribeAndRead e subscriber
          liftIO $ writeIORef subscriptionRef subscription
          pure occ
    let switchInvalidator = runEventM @x $ deferBla $ do
          oldSubscription <- readIORef subscriptionRef
          finalize =<< readIORef wiRef
          writeIORef parentsRef []
          void $ unSpiderHost $ runFrame f  --TODO: Assert that the event isn't firing --TODO: This should not loop because none of the events should be firing, but still, it is inefficient
          -- FIXME: when (isJust occ) $ error $ "Event is firing but it shouldn't?"
          pure oldSubscription -- TODO: not sure that the unsubscribe queue is going to be processed still?
    returnSubscription
          (unsubscribe =<< readIORef subscriptionRef)
          (switchInvalidator, wiRef, subscriptionRef, parentsRef)
          =<< f
  coincidenceUncached coincidenceParent = Event $ \sub -> do
    let f = fmap join
          . mapM (maybe (pure (Just Nothing)) $ \innerE -> do
                                 (subscriptionInner, occInner) <- subscribeAndRead innerE $ Subscriber $ subscriberPropagate sub
                                 deferUnsubscribe subscriptionInner
                                 pure occInner)
    (subscriptionOuter, occOuter) <-
      subscribeAndRead coincidenceParent $ Subscriber $ mapM_ (subscriberPropagate sub) <=< f . Just
    occ <- f occOuter
    returnSubscription (unsubscribe subscriptionOuter) subscriptionOuter occ
  unsafeBuildIncremental readV0 e =
    unsafePerformIO $ do
      putStrLn "unsafeBuildIncremental"
      runEventM @x . R.buildIncremental (R.sample . R.pull $ readV0) $ e
  mergeListUncached :: forall a. (Semigroup a) => [R.Event (SpiderTimeline x) a] -> R.Event (SpiderTimeline x) a
  mergeListUncached es = Event $ \sub -> do
    nodeId <- newNodeId
    liftIO $ putStrLn $ "Merge being subscribed to " <> show nodeId
    clearScheduledRef <- liftIO $ newIORef False
    occRefsSubscriptionsRef <- liftIO $ newIORef $ error "mergeListUncached: occRefsSubscriptions unitialized"
    let maybeResult = do
          res <- fmap (fmap mconcat . sequence) . mapM (readIORef . fst) =<< readIORef occRefsSubscriptionsRef
          printf "Merge state: %s\n" . show . fmap (fmap void) =<< mapM (readIORef . fst) =<< readIORef occRefsSubscriptionsRef
          printf "Merge maybeResult %d: %s\n" nodeId $ anythingToString res
          pure res
    let doScheduleClearOnce = do
          isScheduled <- liftIO $ readIORef clearScheduledRef
          unless isScheduled $ do
            liftIO $ writeIORef clearScheduledRef True
            deferClear $ do
              status <- maybeResult
              when (isNothing status) $
                error "Merge: not all inputs fired"
              liftIO $ writeIORef clearScheduledRef False
              occRefs <- fmap fst <$> readIORef occRefsSubscriptionsRef
              forM_ occRefs (`writeIORef` Nothing)
    liftIO . writeIORef occRefsSubscriptionsRef <=< forM (zip es [(0 :: Int)..]) $ \(e,n) -> do
      liftIO $ printf "Merge starting subscribe of input nr %d\n" n
      occRef <- liftIO $ newIORef Nothing
      subscription <- fmap fst . subscribeWithRec e
        (\_ occ -> do
            liftIO $ printf "Merge %d incoming known occ nr %d: %s\n" nodeId n (anythingToString occ)
            prev <- liftIO $ readIORef occRef
            unless (isNothing prev) $ error $ "merge slot written twice: " <> anythingToString prev <> " to " <> anythingToString occ
            liftIO $ writeIORef occRef (Just occ)
            doScheduleClearOnce
            pure Nothing)
        $ Subscriber $ \_ ->
           mapM_ (\occ -> do
                     liftIO $ printf "Merge %d propagating occ: %s\n" nodeId (anythingToString occ)
                     subscriberPropagate sub occ)
           =<< liftIO maybeResult
      pure (occRef, subscription)
    maybeOcc <- liftIO maybeResult
    returnSubscription (mapM_ (unsubscribe . snd) =<< readIORef occRefsSubscriptionsRef) occRefsSubscriptionsRef maybeOcc
  eventCoercion Coercion = Coercion
  behaviorCoercion Coercion = Coercion

-- INFO: I inlined this from the original
-- newEventWithTriggerIO f = do
--   es <- newFanEventWithTriggerIO $ \Refl -> f
--   return $ R.select es Refl

{-# NOINLINE triggerCtr #-}
triggerCtr :: IORef Int
triggerCtr = unsafePerformIO $ newIORef 0

newEventWithTriggerIO :: forall (x :: Type) a. HasSpiderTimeline x => (RootTrigger x a -> IO (IO ())) -> IO (R.Event (SpiderTimeline x) a)
newEventWithTriggerIO = newEventWithTriggerIO' (_spiderTimeline_rootTriggers (unSTE (spiderTimeline :: SpiderTimelineEnv x)))

newEventWithTriggerIO' :: forall (x :: Type) a. IORef (IntMap (Some (RootTrigger x))) -> (RootTrigger x a -> IO (IO ())) -> IO (R.Event (SpiderTimeline x) a)
newEventWithTriggerIO' rootTriggersRef f = do
  occRef :: (IORef (Maybe (DMap ((:~:) a) Identity))) <- newIORef Nothing
  subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  triggerId <- atomicModifyIORef triggerCtr (\c -> (succ c, c))
  printf "New trigger with id %d\n" triggerId
  pure $ Event $ \sub -> liftIO $ do
    (NewFanSubscribedChildren subscribers uninit) <-
      (\case
        Just res -> pure res
        Nothing -> do
          subscribers <- WeakBag.empty
          let trigger = RootTrigger (triggerId, subscribers, occRef, Refl)
          modifyIORef rootTriggersRef (IntMap.insert triggerId (Some trigger))
          uninit <- f trigger
          let res = NewFanSubscribedChildren subscribers uninit
          modifyIORef' subscribedRef $ DMap.insertWith (error "getRootSubscribed: duplicate key inserted into Root") Refl res
          pure res)
      . DMap.lookup Refl
      =<< readIORef subscribedRef
    sln <- WeakBag.insert' sub subscribers $ do
              uninit
              modifyIORef' subscribedRef $ DMap.delete Refl
              modifyIORef' rootTriggersRef (IntMap.delete triggerId)
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
    occ <- fmap (fmap (coerce . DMap.lookup Refl)) $ readIORef occRef
    printf "newEventTriggerIO': subscribing with occ: %s\n" $ anythingToString occ
    returnSubscription (WeakBag.remove sln >> touch sln) subscribedRef occ

data NewFanSubscribedChildren x a = NewFanSubscribedChildren
  { _newFanSubscribedChildren :: WeakBag (Subscriber x a)
  , _newFanSubscribedUninit :: IO ()
  }

-- TODO: anything in common with Fan?
newFanEventWithTriggerIO :: forall x k. (GCompare k) => (forall a. k a -> RootTrigger x a -> IO (IO ())) -> IO (R.EventSelector (SpiderTimeline x) k)
newFanEventWithTriggerIO f = do
  error "FIXME: temporarily disabled"
  -- occRef <- newIORef DMap.empty
  -- subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  -- return $ R.EventSelector $ \(!k) -> Event $ \sub -> liftIO $ do
  --   (NewFanSubscribedChildren subscribers uninit) <- readIORef subscribedRef >>= (\case
  --     Just res -> pure res
  --     Nothing -> do
  --       subscribers <- WeakBag.empty
  --       uninit <- f k $ RootTrigger (subscribers, occRef, k)
  --       let res = NewFanSubscribedChildren subscribers uninit
  --       modifyIORef' subscribedRef $ DMap.insertWith (error "getRootSubscribed: duplicate key inserted into Root") k res
  --       pure res) . DMap.lookup k
  --   sln <- WeakBag.insert' sub subscribers $ do
  --             uninit
  --             modifyIORef' subscribedRef $ DMap.delete k
  --   -- TODO: understand original intent of this comment:
  --   -- If we die at the same moment that all our children die, they will
  --   -- try to clean us up but will fail because their Weak reference to us
  --   -- will also be dead.  So, if we are dying, check if there are any
  --   -- children; since children don't bother cleaning themselves up if
  --   -- their parents are already dead, I don't think there's a race
  --   -- condition here.  However, if there are any children, then we can
  --   -- infer that we need to clean ourselves up, so we do.
  --   -- finalCleanup = do
  --   --   cs <- readIORef $ _weakBag_children subs
  --   --   when (not $ IntMap.null cs) (cleanupRootSubscribed subscribed)
  --    -- writeIORef weakSelf =<< evaluate =<< mkWeakPtr subscribed (Just finalCleanup)
  --   returnSubscription (WeakBag.remove sln >> touch sln) subscribedRef
  --     . coerce . Just . DMap.lookup k -- TODO: make sure that Just i.e. "(non)occurrence is known" is true
  --     =<< readIORef occRef









-- | Designates the default, global Spider timeline
data SpiderTimeline (x :: Type)

-- | The default, global Spider environment
type Spider = SpiderTimeline Global

-- | A statically allocated 'SpiderTimeline'
data Global

{-# NOINLINE globalSpiderTimelineEnv #-}
globalSpiderTimelineEnv :: SpiderTimelineEnv Global
globalSpiderTimelineEnv = unsafePerformIO unsafeNewSpiderTimelineEnv

class HasSpiderTimeline x where
  -- | Retrieve the current SpiderTimelineEnv
  spiderTimeline :: SpiderTimelineEnv x

instance HasSpiderTimeline Global where
  spiderTimeline = globalSpiderTimelineEnv

data EventLoopException = EventLoopException
instance Exception EventLoopException

instance Show EventLoopException where
  show EventLoopException = "causality loop detected: \n" <>
    "compile reflex with flag 'debug-cycles' and compile with profiling enabled for stack tree"

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

data RootTrigger x a = forall k. GCompare k => RootTrigger (Int, WeakBag (Subscriber x a), IORef (Maybe (DMap k Identity)), k a)

data SpiderEventHandle x a = SpiderEventHandle
  { spiderEventHandleSubscription :: EventSubscription x
  , spiderEventHandleValue :: IORef (Maybe a)
  }

-- | The monad for actions that manipulate a Spider timeline identified by @x@
newtype SpiderHost (x :: Type) a = SpiderHost { unSpiderHost :: IO a } deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadFail)

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE buildHold #-}
  buildHold getV0 e = runFrame . runSpiderHostFrame $ Reflex.Class.buildHold getV0 e
  {-# INLINABLE now #-}
  now = runFrame . runSpiderHostFrame $ Reflex.Class.now

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE sample #-}
  sample = runFrame . R.sample

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  {-# INLINABLE sample #-}
  sample = Reflex.Spider.Internal.ReadPhase . Reflex.Class.sample

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  buildHold getV0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.buildHold getV0 e
  {-# INLINABLE now #-}
  now = Reflex.Spider.Internal.ReadPhase Reflex.Class.now

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHostFrame x) where
  {-# INLINABLE subscribeEvent #-}
  subscribeEvent e = SpiderHostFrame $ do
    --TODO: Unsubscribe eventually (manually and/or with weak ref)
    valRef <- liftIO $ newIORef Nothing
    (subscription, occ) <- subscribeAndRead e $ Subscriber
      { subscriberPropagate = mapM_ (writeAndScheduleClear "subscribeEvent propagate" valRef)
      }
    mapM_ (mapM_ (writeAndScheduleClear "subscribeEvent init" valRef)) occ -- TODO: added but why was this originally not like that?
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

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHost x) where
  newEventWithTrigger = SpiderHost . newEventWithTriggerIO
  newFanEventWithTrigger f = SpiderHost $ newFanEventWithTriggerIO f

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHostFrame x) where
  newEventWithTrigger = SpiderHostFrame . EventM . liftIO . newEventWithTriggerIO
  newFanEventWithTrigger f = SpiderHostFrame $ EventM $ liftIO $ newFanEventWithTriggerIO f

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHost x) where
  {-# INLINABLE subscribeEvent #-}
  subscribeEvent = runFrame . runSpiderHostFrame . Reflex.Host.Class.subscribeEvent

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexHost (SpiderTimeline x) (SpiderHost x) where
  type ReadPhase (SpiderHost x) = Reflex.Spider.Internal.ReadPhase x
  fireEventsAndRead es (Reflex.Spider.Internal.ReadPhase a) = run es a
  runHostFrame = runFrame . runSpiderHostFrame

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

-- | Run an action affecting the global Spider timeline; this will be guarded by
-- a mutex for that timeline
runSpiderHost :: SpiderHost Global a -> IO a
runSpiderHost (SpiderHost a) = a

-- | Run an action affecting a given Spider timeline; this will be guarded by a
-- mutex for that timeline
runSpiderHostForTimeline :: SpiderHost x a -> SpiderTimelineEnv x -> IO a
runSpiderHostForTimeline (SpiderHost a) _ = a

newtype SpiderHostFrame (x :: Type) a = SpiderHostFrame { runSpiderHostFrame :: EventM x a }
  deriving (Functor, Applicative, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadMask, MonadThrow, MonadCatch, R.MonadSample (SpiderTimeline x), R.MonadHold (SpiderTimeline x))

instance Monad (SpiderHostFrame x) where
  {-# INLINABLE (>>=) #-}
  SpiderHostFrame x >>= f = SpiderHostFrame $ x >>= runSpiderHostFrame . f

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

instance HasSpiderTimeline x => NotReady (SpiderTimeline x) (PerformEventT (SpiderTimeline x) (SpiderHost x)) where
  notReadyUntil _ = return ()
  notReady = return ()

instance Eq (SpiderTimelineEnv x) where
  _ == _ = True -- Since only one exists of each type

instance GEq SpiderTimelineEnv where
  a `geq` b = if _spiderTimeline_lock (unSTE a) == _spiderTimeline_lock (unSTE b)
              then Just $ unsafeCoerce Refl -- This unsafeCoerce is safe because the same SpiderTimelineEnv can't have two different 'x' arguments
              else Nothing
