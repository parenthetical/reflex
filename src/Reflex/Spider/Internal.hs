{-# LANGUAGE ApplicativeDo #-}
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
{-# LANGUAGE LambdaCase #-}
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
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Data.Bool (bool)

--NB: Once you subscribe to an Event, you must always hold on the the WHOLE EventSubscription you get back
-- If you do not retain the subscription, you may be prematurely unsubscribed from the parent event.
data EventSubscription x = EventSubscription
  { unsubscribe :: !(IO ())
  , _eventSubscription_subscribed :: {-# UNPACK #-} !(EventSubscribed x)
  }

data Subscriber x a = Subscriber
  { subscriberPropagate :: !(a -> EventM x ())
  , subscriberInvalidateHeight :: !(IO ())
  , subscriberRecalculateHeight :: !(Height -> IO ())
  }

returnSubscription :: Monad m => IO () -> IORef Height -> a -> b -> m (EventSubscription x, b)
returnSubscription cleanup heightRef retained occ =
  return (EventSubscription cleanup (EventSubscribed heightRef (toAny retained)), occ)

subscribeWith :: HasSpiderTimeline x => R.Event (SpiderTimeline x) a -> (a -> EventM x b) -> Subscriber x a -> EventM x (EventSubscription x)
subscribeWith e f = fmap fst . subscribeAndRead (R.pushCheap (\a -> f a >> pure (Just a)) e)

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

-- | Stores all global data relevant to a particular Spider timeline; only one
-- value should exist for each type @x@
newtype SpiderTimelineEnv (x :: Type) = STE {unSTE :: SpiderTimelineEnv' x}
-- We implement SpiderTimelineEnv with a newtype wrapper so
-- we can get the coercions we want safely.

data SpiderTimelineEnv' x = SpiderTimelineEnv
  { _spiderTimeline_lock :: {-# UNPACK #-} !(MVar ())
  , _spiderTimeline_eventEnv :: {-# UNPACK #-} !(EventEnv x)
  }

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

addToQueue :: MonadIO m => a -> IORef [a] -> m ()
addToQueue a q = liftIO $ modifyIORef' q (a:)

deferClear :: forall x. HasSpiderTimeline x => IO () -> EventM x ()
deferClear thunk = addToQueue (Clear thunk) =<< asksEventEnv eventEnvClears

deferMergeUpdate :: HasSpiderTimeline x => EventM x [EventSubscription x] -> IO () -> IO () -> EventM x ()
deferMergeUpdate update invHeight recalcHeight = addToQueue (MergeUpdate update invHeight recalcHeight) =<< asksEventEnv eventEnvMergeUpdates

{-# INLINE writeAndScheduleClear #-}
writeAndScheduleClear :: forall x a. HasSpiderTimeline x => IORef (Maybe a) -> a -> EventM x ()
writeAndScheduleClear ref val = do
  liftIO $ writeIORef ref (Just val)
  deferClear $ writeIORef ref Nothing

data MergeUpdate x = MergeUpdate
  { _mergeUpdate_update :: !(EventM x [EventSubscription x])
  , _mergeUpdate_invalidateHeight :: !(IO ())
  , _mergeUpdate_recalculateHeight :: !(IO ())
  }

newtype SomeInit x = SomeInit { unSomeInit :: EventM x () }

-- EventM can do everything BehaviorM can, plus create holds
newtype EventM x a = EventM { runEventM :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadException, MonadAsyncException, MonadCatch, MonadThrow, MonadMask)

invalidateHeight :: forall {k} {x :: k} {a}. IORef Height -> Subscriber x a -> IO ()
invalidateHeight heightRef sub =  do
    oldHeight <- readIORef heightRef
    -- Don't do anything if the height is already invalid
    when (oldHeight /= invalidHeight) $ do
      writeIORef heightRef $! invalidHeight
      subscriberInvalidateHeight sub

recalculateHeight :: forall {k} {x :: k} {a}. IORef Height -> Subscriber x a -> Height -> IO ()
recalculateHeight heightRef sub maybeNewHeight = do
    currentHeight <- readIORef heightRef
    -- recalculateMyHeight may be called multiple times; perhaps the's a way to finesse it to avoid this check
    -- TODO: This will almost always be true; can we get rid of this check and just proceed to the next one always?
    when (currentHeight == invalidHeight) $ do
      when (maybeNewHeight /= invalidHeight) $ do
        writeIORef heightRef $! maybeNewHeight
        subscriberRecalculateHeight sub maybeNewHeight

getSubscriptionHeight :: forall {k} {x :: k}. EventSubscription x -> IO Height
getSubscriptionHeight = readIORef . eventSubscribedHeightRef . _eventSubscription_subscribed

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
        then do deferClear $ writeIORef occRef $! DMap.empty
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

-- Always refers to 0
{-# NOINLINE zeroRef #-}
zeroRef :: IORef Height
zeroRef = unsafePerformIO $ newIORef zeroHeight

invalidate :: IORef [Weak Invalidator] -> IO ()
invalidate wisRef = do
  mapM_ (\wi -> maybe (pure ()) (\i -> finalize wi >> i) <=< deRefWeak $ wi) =<< readIORef wisRef
  writeIORef wisRef []

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
  mapM_ _mergeUpdate_invalidateHeight mergeUpdates
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

data NewFanSubscribedChildren x a = NewFanSubscribedChildren
  { _newFanSubscribedChildren :: WeakBag (Subscriber x a)
  , _newFanSubscribedUninit :: IO ()
  }

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (EventM x) where
  {-# INLINABLE sample #-}
  sample b = fixmeUnifySample (R.sample b)

fixmeUnifySample :: HasSpiderTimeline x => BehaviorM x b -> EventM x b
fixmeUnifySample readV0 = liftIO . runBehaviorM readV0 Nothing =<< asksEventEnv eventEnvInits

data BehaviorEnv x = BehaviorEnv
  { behaviorEnvMaybeWISubs :: Maybe (Weak Invalidator, IORef [SomeBehaviorSubscribed x])
  , behaviorEnvInitsRef :: IORef [SomeInit x]
  }

-- BehaviorM can sample behaviors
newtype BehaviorM (x :: Type) a = BehaviorM { unBehaviorM :: ReaderIO (BehaviorEnv x) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadReader (BehaviorEnv x))

data BehaviorSubscribed x a
   = BehaviorSubscribedHold (IORef (Maybe (EventSubscription x)))
   | BehaviorSubscribedPull (PullSubscribed x a)

newtype SomeBehaviorSubscribed x = SomeBehaviorSubscribed (Some (BehaviorSubscribed x))

type Invalidator = IO ()

runBehaviorM :: BehaviorM x a -> Maybe (Weak Invalidator, IORef [SomeBehaviorSubscribed x]) -> IORef [SomeInit x] -> IO a
runBehaviorM a mwi holdInits = runReaderIO (unBehaviorM a) (BehaviorEnv mwi holdInits)

addBehaviorSubscribed :: BehaviorSubscribed x a -> BehaviorM x ()
addBehaviorSubscribed h = do
  !m <- asks behaviorEnvMaybeWISubs
  forM_ m $ \(_, !p) -> do
      liftIO $ modifyIORef' p (SomeBehaviorSubscribed (Some h) :)

addThisBehaviorMInvalidator :: IORef [Weak Invalidator] -> BehaviorM x ()
addThisBehaviorMInvalidator invsRef = do
  !m <- asks behaviorEnvMaybeWISubs
  forM_ m $ \(!wi, _) -> do
      liftIO $ modifyIORef' invsRef (wi:)

-- TODO: what is really needed here?
data PullSubscribed x a
   = PullSubscribed { pullSubscribedValue :: !a
                    , pullSubscribedOwnInvalidator :: !Invalidator
                    , pullSubscribedParents :: ![SomeBehaviorSubscribed x] -- Need to keep parent behaviors alive, or they won't let us know when they're invalidated
                    }

deferInit :: forall x. HasSpiderTimeline x => EventM x () -> EventM x ()
deferInit i = addToQueue (SomeInit i) =<< asksEventEnv eventEnvInits

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (EventM x) where
  {-# NOINLINE buildHold #-}
  -- Note: cannot examine its event until after the phase is over
  buildHold readV0 e = do
    invsRef <- liftIO $ newIORef [] -- invalidators
    parentRef <- liftIO $ newIORef Nothing
    let forceLazyHoldReturnValRef = unsafePerformIO . runEventM @x $ do -- This originally used custom lazy caching code, replaced with unsafePerformIO
         valRef <- liftIO . newIORef =<< readV0
         deferInit $ do
           maybeParent <- liftIO $ readIORef parentRef
           when (isNothing maybeParent) $ do
             liftIO . writeIORef parentRef . Just
               <=< subscribeWith e (\a -> do
                                       vRef <- pure $! valRef
                                       iRef <- pure $! invsRef
                                       addToQueue (SomeAssignment @x vRef iRef a) =<< asksEventEnv eventEnvAssignments)
               $ Subscriber (const (pure ())) (pure ()) (const (pure ()))
         pure valRef
    deferInit @x $ void $ liftIO $ evaluate forceLazyHoldReturnValRef
    pure $ Behavior $ do
          addBehaviorSubscribed (BehaviorSubscribedHold parentRef)
          addThisBehaviorMInvalidator invsRef
          liftIO $ readIORef forceLazyHoldReturnValRef
  {-# INLINABLE now #-}
  now = do
    nowOrNot <- liftIO $ newIORef $ Just ()
    deferClear $ writeIORef nowOrNot Nothing
    return . Event $ \_ -> do
      occ <- liftIO . readIORef $ nowOrNot
      returnSubscription (pure ()) zeroRef () occ

instance Reflex.Class.MonadSample (SpiderTimeline x) (BehaviorM x) where
  {-# INLINABLE sample #-}
  sample = readBehaviorTracked

instance HasSpiderTimeline x => R.Reflex (SpiderTimeline x) where
  {-# SPECIALIZE instance R.Reflex (SpiderTimeline Global) #-}
  newtype Behavior (SpiderTimeline x) a = Behavior { readBehaviorTracked :: BehaviorM x a }
  newtype Event (SpiderTimeline x) a = Event { subscribeAndRead :: Subscriber x a -> EventM x (EventSubscription x, Maybe a) }
  type PullM (SpiderTimeline x) = BehaviorM x
  type PushM (SpiderTimeline x) = EventM x
  {-# INLINABLE never #-}
  never = Event $ const $ returnSubscription (pure ()) zeroRef () Nothing
  --TODO: Try a caching strategy where we subscribe directly to the parent when
  --there's only one subscriber, and then build our own FastWeakBag only when a second
  --subscriber joins
  {-# NOINLINE [0] cacheEvent #-}
  cacheEvent :: forall a. R.Event (SpiderTimeline x) a -> R.Event (SpiderTimeline x) a
  cacheEvent e = unsafePerformIO $ do
    subscribers :: WeakBag (Subscriber x a) <- WeakBag.empty
    parentSubscriptionRef :: IORef (EventSubscription x) <- newIORef $ error "cacheEvent: parentRef uninitialized"
    occRef :: IORef (Maybe a) <- newIORef Nothing
    pure $ Event $ \sub -> do
      liftIO (WeakBag.null subscribers) >>= flip when (
        liftIO . writeIORef parentSubscriptionRef
        <=< subscribeWith e (writeAndScheduleClear occRef) $ Subscriber
            { subscriberPropagate = flip propagate subscribers
            , subscriberInvalidateHeight = WeakBag.traverse_ subscribers subscriberInvalidateHeight
            , subscriberRecalculateHeight = WeakBag.traverse_ subscribers . flip subscriberRecalculateHeight
            })
      parentSub <- liftIO $ readIORef parentSubscriptionRef
      sln <- liftIO $ WeakBag.insert' sub subscribers $ unsubscribe parentSub
      returnSubscription (WeakBag.remove sln >> touch sln)
                         (eventSubscribedHeightRef $ _eventSubscription_subscribed parentSub)
                         (sln, parentSubscriptionRef)
                         <=< liftIO $ readIORef occRef
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
  pull a = unsafePerformIO $ do
    ref :: IORef (Maybe (PullSubscribed x a)) <- newIORef Nothing
    invsRef :: IORef [Weak Invalidator] <- newIORef []
    pure $ Behavior $ do
      subscribed <- liftIO (readIORef ref) >>= maybe (do
                      let i = readIORef ref
                              >>= mapM_ (const $ do
                                            writeIORef ref Nothing
                                            invalidate invsRef)
                      wi <- liftIO $ mkWeakPtrWithDebug i
                      parentsRef <- liftIO $ newIORef []
                      !holdInits <- BehaviorM $ asks behaviorEnvInitsRef
                      aVal <- liftIO $ runReaderIO (unBehaviorM a) (BehaviorEnv (Just (wi, parentsRef)) holdInits)
                      parents <- liftIO $ readIORef parentsRef
                      let subscribed = PullSubscribed
                            { pullSubscribedValue = aVal
                            , pullSubscribedOwnInvalidator = i
                            , pullSubscribedParents = parents
                            }
                      liftIO $ writeIORef ref $ Just subscribed
                      return subscribed)
                    pure
      addBehaviorSubscribed (BehaviorSubscribedPull subscribed)
      addThisBehaviorMInvalidator invsRef
      pure $ pullSubscribedValue subscribed
  switchUncached switchParent = Event $ \sub -> do
    heightRef <- liftIO $ newIORef $ error "switchUncached: heightRef uninitialized"
    ownWeakInvalidatorRef :: IORef (Weak Invalidator) <- liftIO $ newIORef $ error "switch: ownWeakInvalidatorRef uninitialized"
    let subscriber = Subscriber (subscriberPropagate sub) (invalidateHeight heightRef sub) (recalculateHeight heightRef sub)
    let writeNewWeakInvalidator i = do
          wi <- mkWeakPtrWithDebug i
          writeIORef ownWeakInvalidatorRef $! wi
    liftIO $ writeNewWeakInvalidator (pure ())
    ownInvalidatorRef <- liftIO $ newIORef $ error "switch: ownInvalidatorRef uninitialized"
    -- withB is like "fold over Behavior updates"
    let withB :: forall s b. s -> R.Behavior (SpiderTimeline x) b -> (s -> b -> EventM x s) -> EventM x s
        withB currentState b f = mfix $ \newState -> do
         let ownInvalidator = runEventM @x $ deferClear $ do
               putStrLn "Running inits inside switch"
               -- TODO: this used to be runFrame instead of justRunInits but in the tests only inits are generated, also it now loops if you use runFrame (if you defer to MergeUpdate it doesn't loop).
               unSpiderHost . justRunInits $ void $ withB newState b f
         liftIO $ writeIORef ownInvalidatorRef ownInvalidator
         liftIO $ finalize =<< readIORef ownWeakInvalidatorRef
         liftIO $ writeNewWeakInvalidator ownInvalidator
         f currentState <=< liftIO $ do
           wi <- readIORef ownWeakInvalidatorRef
           initsRef <- newIORef [] -- TODO: normally initsRef <- getDeferralQueue, but here the initsRef stays empty?
           parentsRef <- newIORef []
           runBehaviorM (R.sample b) (Just (wi, parentsRef)) initsRef
    (unsubscribeSubscription :: IO (), parentOcc) <- withB (pure (), Nothing) switchParent $ \(unsubscribePrevious,_) e -> do
          liftIO unsubscribePrevious
          (subscription, occ) <- subscribeAndRead e subscriber
          liftIO $ writeIORef heightRef =<< getSubscriptionHeight subscription
          pure (runEventM @x $ deferMergeUpdate
                          (pure [subscription])
                          (invalidateHeight heightRef sub)
                          (recalculateHeight heightRef sub =<< getSubscriptionHeight subscription)
               , occ)
    returnSubscription
      (unsubscribeSubscription >> (finalize =<< readIORef ownWeakInvalidatorRef))
      heightRef
      ownInvalidatorRef
      parentOcc
  coincidenceUncached coincidenceParent = Event $ \sub -> do
    heightRef <- liftIO $ newIORef zeroHeight
    let subscriber = Subscriber (subscriberPropagate sub) (invalidateHeight heightRef sub) (recalculateHeight heightRef sub)
    (subscription, occ) <-
      subscribeAndRead (R.pushCheap (\e -> do
                                      (subscription, mocc) <- subscribeAndRead e subscriber
                                      innerHeight <- liftIO $ getSubscriptionHeight subscription
                                      currentHeight <- liftIO $ readIORef heightRef
                                      deferMergeUpdate (pure [subscription])
                                              (invalidateHeight heightRef sub)
                                              (recalculateHeight heightRef sub =<< getSubscriptionHeight subscription)
                                      when (innerHeight > currentHeight) $ liftIO $ do 
                                        writeIORef heightRef innerHeight
                                        subscriberInvalidateHeight sub
                                        subscriberRecalculateHeight sub innerHeight
                                      pure mocc)
                       coincidenceParent)
      subscriber
    liftIO $ modifyIORef heightRef . max =<< getSubscriptionHeight subscription
    returnSubscription (unsubscribe subscription) heightRef subscription occ
  unsafeBuildIncremental readV0 v' =
    -- TODO: using buildIncremental is lazier than the original implementation (because of the double Init scheduling)
    unsafePerformIO . runEventM @x $ R.buildIncremental (fixmeUnifySample readV0) v'
    -- TODO: why can't we do this? QueryT tests fail but others are fine (although they might not use unsafeBuild):
    -- SpiderIncremental $ Dynamic (Behavior readV0) v'
  mergeListUncached :: forall a. (Semigroup a) => [R.Event (SpiderTimeline x) a] -> R.Event (SpiderTimeline x) a
  mergeListUncached es = Event $ \sub -> do
    heightRef <- liftIO $ newIORef zeroHeight
    accumRef :: IORef (Maybe a) <- liftIO $ newIORef Nothing
    subscriptionsRef <- liftIO $ newIORef []
    let getMaybeHeight = do
          subs <- mapM (readIORef . eventSubscribedHeightRef . _eventSubscription_subscribed) =<< readIORef subscriptionsRef
          pure $ if invalidHeight `elem` subs then invalidHeight else let (Height h) = maximum (zeroHeight:subs) in Height (succ h)
    let seenAllEvents = (<=) <$> liftIO (readIORef heightRef) <*> (liftIO . readIORef =<< asksEventEnv eventEnvCurrentHeight)
    delayedRef <- asksEventEnv eventEnvDelayedMerges
    liftIO . writeIORef subscriptionsRef <=< forM es $ \e ->
      subscribeWith e
      (\a -> do
             maybePrevAccumVal <- liftIO $ readIORef accumRef
             liftIO $ writeIORef accumRef (Just a <> maybePrevAccumVal)
             liftIO $ do height <- readIORef heightRef
                         when (height == invalidHeight) $
                           throwIO EventLoopException
             when (isNothing maybePrevAccumVal) $ do -- Only schedule the firing once
               let scheduleMerge' (Height initialHeight) =
                     liftIO $ modifyIORef' delayedRef $ IntMap.insertWith (++) initialHeight [do
                       seenAllEvents >>= bool (scheduleMerge' =<< liftIO (readIORef heightRef)) (do
                           maybeCurrentAccumVal <- liftIO $ readIORef accumRef
                           when (isJust maybeCurrentAccumVal) $ do
                             mapM_ (subscriberPropagate sub) maybeCurrentAccumVal
                             liftIO $ writeIORef accumRef Nothing)]
               scheduleMerge' <=< liftIO $ readIORef heightRef
             pure (Just ()))
        $ Subscriber (const (pure ())) (invalidateHeight heightRef sub) $ \_ -> do
          currentHeight <- readIORef heightRef
          when (currentHeight == invalidHeight) $ do
            maybeNewHeight <- getMaybeHeight
            when (maybeNewHeight /= invalidHeight) $ do
              writeIORef heightRef $! maybeNewHeight
              subscriberRecalculateHeight sub maybeNewHeight
    liftIO $ writeIORef heightRef =<< getMaybeHeight
    occ <- runMaybeT $ do
      guard =<< lift seenAllEvents
      liftIO $ atomicModifyIORef accumRef (Nothing,)
    returnSubscription (mapM_ unsubscribe =<< readIORef subscriptionsRef) heightRef subscriptionsRef (join occ)
  eventCoercion Coercion = Coercion
  behaviorCoercion Coercion = Coercion








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

data RootTrigger x a = forall k. GCompare k => RootTrigger (WeakBag (Subscriber x a), IORef (DMap k Identity), k a)

data SpiderEventHandle x a = SpiderEventHandle
  { spiderEventHandleSubscription :: EventSubscription x
  , spiderEventHandleValue :: IORef (Maybe a)
  }

-- | The monad for actions that manipulate a Spider timeline identified by @x@
newtype SpiderHost (x :: Type) a = SpiderHost { unSpiderHost :: IO a } deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadFail)

-- TODO: anything in common with Fan?
newFanEventWithTriggerIO :: forall x k. (GCompare k) => (forall a. k a -> RootTrigger x a -> IO (IO ())) -> IO (R.EventSelector (SpiderTimeline x) k)
newFanEventWithTriggerIO f = do
  occRef <- newIORef DMap.empty
  subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  return $ R.EventSelector $ \(!k) -> Event $ \sub -> liftIO $ do
    (NewFanSubscribedChildren subscribers uninit) <- readIORef subscribedRef >>= (\case
      Just res -> pure res
      Nothing -> do
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
    subscription <- fmap fst . subscribeAndRead e $ Subscriber
      { subscriberPropagate = writeAndScheduleClear valRef
      , subscriberInvalidateHeight = pure ()
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
  newFanEventWithTrigger f = SpiderHost $ newFanEventWithTriggerIO f

instance Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHostFrame x) where
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

newEventWithTriggerIO :: forall (x :: Type) a. (RootTrigger x a -> IO (IO ())) -> IO (R.Event (SpiderTimeline x) a)
newEventWithTriggerIO f = do
  es <- newFanEventWithTriggerIO $ \Refl -> f
  return $ R.select es Refl

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

