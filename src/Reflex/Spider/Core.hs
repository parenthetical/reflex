{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}

#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
{-# OPTIONS_GHC -Wunused-binds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}

module Reflex.Spider.Core
( EventSelectorG(selectG),
      EventSelector(select),
      EventSelectorInt(selectInt),
      Dyn,
      EventM(EventM),
      BehaviorM(BehaviorM),
      HasSpiderTimeline,
      SpiderTimelineEnv,
      Global,
      Dynamic(dynamicUpdated, dynamicCurrent),
      DynamicS,
      Behavior(..),
      Subscriber(Subscriber, subscriberRecalculateHeight,
                 subscriberPropagate, subscriberInvalidateHeight),
      Event(Event),
      pushCheap,
      headE,
      now,
      subscribe,
      eventNever,
      behaviorHoldIdentity,
      behaviorConst,
      readBehaviorUntracked,
      dynamicHold,
      dynamicHoldIdentity,
      dynamicConst,
      dynamicDyn,
      dynamicDynIdentity,
      writeAndScheduleClear,
      hold,
      newMapDyn,
      buildDynamic,
      unsafeBuildDynamic,
      push,
      pull,
      switch,
      coincidence,
      run,
      fanInt,
      mergeInt,
      mergeG,
      mergeWithMove,
      fanG,
      runFrame,
      SpiderPushM(..),
      SpiderPullM(..),
      SpiderEventHandle(..),
      RootTrigger,
      SpiderHost(SpiderHost),
      newFanEventWithTriggerIO,
      newSpiderTimeline,
      withSpiderTimeline,
      subscribeAndRead,
      EventLoopException
      )
where
import Control.Concurrent
import Control.Exception
import Control.Monad hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Catch (MonadMask, MonadThrow, MonadCatch)
import Control.Monad.Exception
import Control.Monad.Fix
import Control.Monad.Identity hiding (forM, forM_, mapM, mapM_)
import Control.Monad.Primitive
import Control.Monad.Reader.Class
import Control.Monad.IO.Class
import Control.Monad.ReaderIO
import Data.Coerce
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum (..))
import qualified Data.FastMutableIntMap as FastMutableIntMap
import Data.Foldable hiding (concat, elem, sequence_)
import Data.Functor.Constant
import Data.Functor.Misc
import Data.Functor.Product
import Data.GADT.Compare
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IORef
import Data.Kind (Type)
import Data.Maybe hiding (mapMaybe)
import Data.Proxy
import Data.Traversable
import Data.Type.Equality ((:~:)(Refl))
import Data.Witherable (mapMaybe)
import GHC.Exts hiding (toList)
import GHC.IORef (IORef (..))
import GHC.Stack
import System.IO.Unsafe
import System.Mem.Weak
import Unsafe.Coerce

#ifdef DEBUG_CYCLES
import Control.Monad.State hiding (forM, forM_, mapM, mapM_, sequence)
#endif

import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Tree (Forest, Tree (..), drawForest)

import Data.FastWeakBag (FastWeakBag)
import qualified Data.FastWeakBag as FastWeakBag

import Data.Reflection
import Data.Some (Some(Some))
import Data.WeakBag (WeakBag)
import qualified Data.WeakBag as WeakBag
import Data.Patch
import qualified Data.Patch.DMap as PatchDMap
import qualified Data.Patch.DMapWithMove as PatchDMapWithMove
import qualified Control.Monad.Writer as W
import Control.Monad.Writer (WriterT)
import Control.Monad.Trans.Maybe
#ifdef DEBUG_TRACE_EVENTS
import qualified Data.ByteString.Char8 as BS8
import System.IO (stderr)
import Data.List (isPrefixOf)
#endif


whenM :: Monad m => m Bool -> m () -> m ()
whenM mcond m = mcond >>= flip when m

-- TODO stdout might not be the best channel for debug output
debugStrLn :: String -> IO ()
debugStrLn = putStrLn

#ifdef DEBUG_TRACE_EVENTS
withStackOneLine :: (BS8.ByteString -> a) -> a
withStackOneLine expr = unsafePerformIO $ do
  stack <- currentCallStack
  return (expr . BS8.pack  . unwords . dropInternal . reverse $ stack)
    where dropInternal = filterStack "Reflex.Spider.Internal"

#endif

debugPropagate :: Bool

debugInvalidateHeight :: Bool

debugInvalidate :: Bool

#ifdef DEBUG
#define DEBUG_NODEIDS

#ifdef DEBUG_TRACE_PROPAGATION
debugPropagate = True
#else
debugPropagate = False
#endif

#ifdef DEBUG_TRACE_HEIGHT
debugInvalidateHeight = True
#else
debugInvalidateHeight = False
#endif

#ifdef DEBUG_TRACE_INVALIDATION
debugInvalidate = True
#else
debugInvalidate = False
#endif

showNodeId' :: Int -> String
showNodeId' = ("#"<>) . show


#else

debugPropagate = False
debugInvalidateHeight = False
debugInvalidate = False

nodeId :: Int 
nodeId = error "nodeId was evaluated without DEBUG turned on"

-- This must be inline, or error messages will cause memory leaks due to retaining the node in question
{-# INLINE showNodeId #-}
showNodeId :: a -> String
showNodeId _ = ""

{-# INLINE showNodeId' #-}
showNodeId' :: Int -> String
showNodeId' _ = ""

#endif

#ifdef DEBUG_NODEIDS
{-# NOINLINE nextNodeIdRef #-}
nextNodeIdRef :: IORef Int
nextNodeIdRef = unsafePerformIO $ newIORef 1

newNodeId :: IO Int
newNodeId = atomicModifyIORef' nextNodeIdRef $ \n -> (succ n, n)
#endif

--------------------------------------------------------------------------------
-- EventSubscription
--------------------------------------------------------------------------------

--NB: Once you subscribe to an Event, you must always hold on the the WHOLE EventSubscription you get back
-- If you do not retain the subscription, you may be prematurely unsubscribed from the parent event.
data EventSubscription x = EventSubscription
  { _eventSubscription_unsubscribe :: !(IO ())
  , _eventSubscription_subscribed :: {-# UNPACK #-} !(EventSubscribed x)
  }

unsubscribe :: EventSubscription x -> IO ()
unsubscribe (EventSubscription u _) = u


--------------------------------------------------------------------------------
-- Event
--------------------------------------------------------------------------------

newtype Event x a = Event { unEvent :: Subscriber x a -> EventM x (EventSubscription x, Maybe a) }

{-# INLINE subscribeAndRead #-}
subscribeAndRead :: Event x a -> Subscriber x a -> EventM x (EventSubscription x, Maybe a)
subscribeAndRead = unEvent

subscribeAndReadWithHeight :: Event x a -> Subscriber x a -> EventM x (EventSubscription x, Height, Maybe a)
subscribeAndReadWithHeight e subscriber = do
  (subscription@(EventSubscription _ subd), occ) <- subscribeAndRead e subscriber
  height <- liftIO $ getEventSubscribedHeight subd
  pure (subscription, height, occ)
  

{-# RULES
"cacheEvent/cacheEvent" forall e. cacheEvent (cacheEvent e) = cacheEvent e
"cacheEvent/pushCheap" forall f e. pushCheap f (cacheEvent e) = cacheEvent (pushCheap f e)
"hold/cacheEvent" forall f e. hold f (cacheEvent e) = hold f e
  #-}

-- | Construct an 'Event' equivalent to that constructed by 'push', but with no
-- caching; if the computation function is very cheap, this is (much) more
-- efficient than 'push'
{-# INLINE [1] pushCheap #-}
pushCheap :: HasSpiderTimeline x => (a -> EventM x (Maybe b)) -> Event x a -> Event x b
pushCheap !f e = Event $ \sub -> do
  (subscription, occ) <- subscribeAndRead e $ debugSubscriber' "push" $ sub
    { subscriberPropagate = \a -> do
        mb <- f a
        mapM_ (subscriberPropagate sub) mb
    }
  occ' <- join <$> mapM f occ
  return (subscription, occ')

--TODO: Make this lazy in its input event
headE :: forall x m a. (Defer (SomeInit x) m, HasSpiderTimeline x) => Event x a -> m (Event x a)
headE originalE = do
  let -- | Subscribe to an Event only for the duration of one occurrence
      subscribeAndReadHead :: Event x a -> Subscriber x a -> EventM x (EventSubscription x, Maybe a)
      subscribeAndReadHead e sub = do
        subscriptionRef <- liftIO $ newIORef $ error "subscribeAndReadHead: not initialized"
        (subscription, occ) <- subscribeAndRead e $ debugSubscriber' "head" $ sub
          { subscriberPropagate = \a -> do
              liftIO $ unsubscribe =<< readIORef subscriptionRef
              subscriberPropagate sub a
          }
        liftIO $ case occ of
          Nothing -> writeIORef subscriptionRef $! subscription
          Just _ -> unsubscribe subscription
        return (subscription, occ)
  parent <- liftIO $ newIORef $ Just originalE
  defer $ SomeInit $ do --TODO: Rename SomeInit appropriately
    let clearParent = liftIO $ writeIORef parent Nothing
    (_, occ) <- subscribeAndReadHead originalE $
      Subscriber
      { subscriberPropagate = \_ -> clearParent
      , subscriberInvalidateHeight = \_ -> return ()
      , subscriberRecalculateHeight = \_ -> return ()
      }
    when (isJust occ) clearParent
  return $ Event $ \sub ->
    liftIO (readIORef parent) >>= \case
      Nothing -> subscribeAndReadNever
      Just e -> subscribeAndReadHead e sub

now :: ( MonadIO m, Defer (Some Clear) m, HasSpiderTimeline x
        ) => m (Event x ())
now = do
  nowOrNot <- liftIO $ newIORef $ Just ()
  scheduleClear nowOrNot
  return . Event $ \_ -> do
    occ <- liftIO . readIORef $ nowOrNot
    return ( EventSubscription
             (return ())
             (EventSubscribed
              { eventSubscribedHeightRef = zeroRef
              , eventSubscribedRetained = toAny ()
#ifdef DEBUG_CYCLES
              , eventSubscribedGetParents = return []
              , eventSubscribedHasOwnHeightRef = False
              , eventSubscribedWhoCreated = return ["now"]
#endif
              })
           , occ
           )

-- | Construct an 'Event' whose value is guaranteed not to be recomputed
-- repeatedly
--
--TODO: Try a caching strategy where we subscribe directly to the parent when
--there's only one subscriber, and then build our own FastWeakBag only when a second
--subscriber joins
{-# NOINLINE [0] cacheEvent #-}
cacheEvent :: forall x a. HasSpiderTimeline x => Event x a -> Event x a
cacheEvent e = unsafePerformIO $ do
  subscribers :: WeakBag (Subscriber x a) <- WeakBag.empty
  parentSubscriptionRef :: IORef (EventSubscription x) <- newIORef $ error "cacheEvent: parentRef uninitialized"
  occRef :: IORef (Maybe a) <- newIORef Nothing
#ifdef DEBUG_NODEIDS
  nodeId <- liftIO newNodeId
#endif
  pure $ Event $ \sub -> {-# SCC "cacheEvent" #-} do
    whenM (liftIO (WeakBag.null subscribers)) $ do
      (parentSub, occ) <- subscribeAndRead e $ debugSubscriber' ("cacheEvent" <> showNodeId' nodeId) $
        Subscriber
          { subscriberPropagate = \a -> do
              writeAndScheduleClear occRef a
              propagate a subscribers
          , subscriberInvalidateHeight = WeakBag.traverse_ subscribers . invalidateSubscriberHeight
          , subscriberRecalculateHeight = WeakBag.traverse_ subscribers . recalculateSubscriberHeight
          }
      mapM_ (writeAndScheduleClear occRef) occ
      liftIO $ writeIORef parentSubscriptionRef parentSub
    parentSub <- liftIO $ readIORef parentSubscriptionRef
    sln <- liftIO $ WeakBag.insert' sub subscribers $ unsubscribe parentSub
    occ <- liftIO $ readIORef occRef
    pure ( EventSubscription
           (WeakBag.remove sln >> touch sln)
           (EventSubscribed
              { eventSubscribedHeightRef = eventSubscribedHeightRef $ _eventSubscription_subscribed parentSub
              , eventSubscribedRetained = toAny (sln, parentSubscriptionRef)
#ifdef DEBUG_CYCLES
              , eventSubscribedGetParents = pure [_eventSubscription_subscribed parentSub]
              , eventSubscribedHasOwnHeightRef = False
              , eventSubscribedWhoCreated = whoCreatedIORef occRef
#endif
              }
           )
         , occ
         )


subscribe :: Event x a -> Subscriber x a -> EventM x (EventSubscription x)
subscribe e s = fst <$> subscribeAndRead e s

subscribeAndReadNever :: EventM x (EventSubscription x, Maybe a)
subscribeAndReadNever = return (EventSubscription (return ())
                                (EventSubscribed
                                  { eventSubscribedHeightRef = zeroRef
                                  , eventSubscribedRetained = toAny ()
#ifdef DEBUG_CYCLES
                                  , eventSubscribedGetParents = return []
                                  , eventSubscribedHasOwnHeightRef = False
                                  , eventSubscribedWhoCreated = return ["never"]
#endif
                                  }),
                                Nothing)

eventNever :: Event x a
eventNever = Event $ const subscribeAndReadNever

--------------------------------------------------------------------------------
-- Subscriber
--------------------------------------------------------------------------------

data Subscriber x a = Subscriber
  { subscriberPropagate :: !(a -> EventM x ())
  , subscriberInvalidateHeight :: !(Height -> IO ())
  , subscriberRecalculateHeight :: !(Height -> IO ())
  }

invalidateSubscriberHeight :: Height -> Subscriber x a -> IO ()
invalidateSubscriberHeight = flip subscriberInvalidateHeight

recalculateSubscriberHeight :: Height -> Subscriber x a -> IO ()
recalculateSubscriberHeight = flip subscriberRecalculateHeight

-- | Propagate everything at the current height
propagate :: forall x a. HasSpiderTimeline x => a -> WeakBag (Subscriber x a) -> EventM x ()
propagate a subscribers = withIncreasedDepth (Proxy::Proxy x) $
  -- Note: in the following traversal, we do not visit nodes that are added to the list during our traversal; they are new events, which will necessarily have full information already, so there is no need to traverse them
  --TODO: Should we check if nodes already have their values before propagating?  Maybe we're re-doing work
  WeakBag.traverse_ subscribers $ \s -> subscriberPropagate s a

-- | Propagate everything at the current height
propagateFast :: forall x a. HasSpiderTimeline x => a -> FastWeakBag (Subscriber x a) -> EventM x ()
propagateFast a subscribers = withIncreasedDepth (Proxy::Proxy x) $
  -- Note: in the following traversal, we do not visit nodes that are added to the list during our traversal; they are new events, which will necessarily have full information already, so there is no need to traverse them
  --TODO: Should we check if nodes already have their values before propagating?  Maybe we're re-doing work
  FastWeakBag.traverse_ subscribers $ \s -> subscriberPropagate s a

--------------------------------------------------------------------------------
-- EventSubscribed
--------------------------------------------------------------------------------

toAny :: a -> Any
toAny = unsafeCoerce

-- Why do we use Any here, instead of just giving eventSubscribedRetained an
-- existential type? Sadly, GHC does not currently know how to unbox types
-- with existentially quantified fields. So instead we just coerce values
-- to type Any on the way in. Since we never coerce them back, this is
-- perfectly safe.
data EventSubscribed x = EventSubscribed
  { eventSubscribedHeightRef :: {-# UNPACK #-} !(IORef Height)
  , eventSubscribedRetained :: {-# NOUNPACK #-} !Any
#ifdef DEBUG_CYCLES
  , eventSubscribedGetParents :: !(IO [EventSubscribed x]) -- For debugging loops
  , eventSubscribedHasOwnHeightRef :: !Bool
  , eventSubscribedWhoCreated :: !(IO [String])
#endif
  }

-- TODO: make sure this is used
getEventSubscribedHeight :: EventSubscribed x -> IO Height
getEventSubscribedHeight es = readIORef $ eventSubscribedHeightRef es

#ifdef DEBUG_CYCLES
whoCreatedEventSubscribed :: EventSubscribed x -> IO [String]
whoCreatedEventSubscribed = eventSubscribedWhoCreated

walkInvalidHeightParents :: EventSubscribed x -> IO [EventSubscribed x]
walkInvalidHeightParents s0 = do
  subscribers <- flip execStateT mempty $ ($ s0) $ fix $ \loop s -> do
    h <- liftIO $ readIORef $ eventSubscribedHeightRef s
    when (h == invalidHeight) $ do
      when (eventSubscribedHasOwnHeightRef s) $ liftIO $ writeIORef (eventSubscribedHeightRef s) $! invalidHeightBeingTraversed
      modify (s :)
      mapM_ loop =<< liftIO (eventSubscribedGetParents s)
  forM_ subscribers $ \s -> writeIORef (eventSubscribedHeightRef s) $! invalidHeight
  return subscribers
#endif

{-# INLINE subscribeHoldEvent #-}
subscribeHoldEvent :: Hold x p -> Subscriber x p -> EventM x (EventSubscription x, Maybe p)
subscribeHoldEvent = subscribeAndRead . holdEvent

--------------------------------------------------------------------------------
-- Behavior
--------------------------------------------------------------------------------

newtype Behavior x a = Behavior { readBehaviorTracked :: BehaviorM x a }

behaviorHold :: Hold x p -> Behavior x (PatchTarget p)
behaviorHold !h = Behavior $ readHoldTracked h

behaviorHoldIdentity :: Hold x (Identity a) -> Behavior x a
behaviorHoldIdentity = behaviorHold

behaviorConst :: a -> Behavior x a
behaviorConst !a = Behavior $ return a

{-# INLINE readHoldTracked #-}
readHoldTracked :: Hold x p -> BehaviorM x (PatchTarget p)
readHoldTracked h = do
  result <- liftIO $ readIORef $ holdValue h
  askInvalidator >>= mapM_ (\wi -> liftIO $ modifyIORef' (holdInvalidators h) (wi:))
  addParentB (BehaviorSubscribedHold h)
  liftIO $ touch h -- Otherwise, if this gets inlined enough, the hold's parent reference may get collected
  return result

{-# INLINABLE readBehaviorUntracked #-}
readBehaviorUntracked :: Defer (SomeHoldInit x) m => Behavior x a -> m a
readBehaviorUntracked b = do
  holdInits <- getDeferralQueue
  liftIO $ runBehaviorM (readBehaviorTracked b) Nothing holdInits --TODO: Specialize readBehaviorTracked to the Nothing and Just cases

--------------------------------------------------------------------------------
-- Dynamic
--------------------------------------------------------------------------------

type DynamicS x p = Dynamic x (PatchTarget p) p

data Dynamic x target p = Dynamic
  { dynamicCurrent :: !(Behavior x target)
  , dynamicUpdated :: Event x p -- This must be lazy; see the comment on holdEvent --TODO: Would this let us eliminate `Dyn`?
  }

deriving instance (HasSpiderTimeline x) => Functor (Dynamic x target)




dynamicHold :: Hold x p -> DynamicS x p
dynamicHold !h = Dynamic
  { dynamicCurrent = behaviorHold h
  , dynamicUpdated = Event $ subscribeHoldEvent h
  }

dynamicHoldIdentity :: Hold x (Identity a) -> DynamicS x (Identity a)
dynamicHoldIdentity = dynamicHold

dynamicConst :: PatchTarget p -> DynamicS x p
dynamicConst !a = Dynamic
  { dynamicCurrent = behaviorConst a
  , dynamicUpdated = eventNever
  }

dynamicDyn :: (HasSpiderTimeline x, Patch p) => Dyn x p -> DynamicS x p
dynamicDyn !d = Dynamic
  { dynamicCurrent = Behavior $ readHoldTracked =<< getDynHold d
  , dynamicUpdated = Event $ \sub -> getDynHold d >>= \h -> subscribeHoldEvent h sub
  }

dynamicDynIdentity :: HasSpiderTimeline x => Dyn x (Identity a) -> DynamicS x (Identity a)
dynamicDynIdentity = dynamicDyn

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

--type role Hold representational
data Hold x p
   = Hold { holdValue :: !(IORef (PatchTarget p))
          , holdInvalidators :: !(IORef [Weak (Invalidator x)])
          , holdEvent :: Event x p -- This must be lazy, or holds cannot be defined before their input Events
          , holdParent :: !(IORef (Maybe (EventSubscription x))) -- Keeps its parent alive (will be undefined until the hold is initialized) --TODO: Probably shouldn't be an IORef
          }

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
#ifdef DEBUG
  , _spiderTimeline_depth :: {-# UNPACK #-} !(IORef Int)
#endif
  }

-- type role SpiderTimelineEnv' nominal

instance Eq (SpiderTimelineEnv x) where
  _ == _ = True -- Since only one exists of each type

instance GEq SpiderTimelineEnv where
  a `geq` b = if _spiderTimeline_lock (unSTE a) == _spiderTimeline_lock (unSTE b)
              then Just $ unsafeCoerce Refl -- This unsafeCoerce is safe because the same SpiderTimelineEnv can't have two different 'x' arguments
              else Nothing

data EventEnv x
   = EventEnv { eventEnvAssignments :: !(IORef [SomeAssignment x]) -- Needed for Subscribe
              , eventEnvHoldInits :: !(IORef [SomeHoldInit x]) -- Needed for Subscribe
              , eventEnvMergeUpdates :: !(IORef [SomeMergeUpdate x])
              , eventEnvInits :: !(IORef [SomeInit x]) -- Needed for Subscribe
              , eventEnvClears :: !(IORef [Some Clear]) -- Needed for Subscribe
              , eventEnvIntClears :: !(IORef [Some IntClear])
              , eventEnvRootClears :: !(IORef [Some RootClear])
              , eventEnvCurrentHeight :: !(IORef Height) -- Needed for Subscribe
              , eventEnvDelayedMerges :: !(IORef (IntMap [EventM x ()]))
              }

{-# INLINE runEventM #-}
runEventM :: EventM x a -> IO a
runEventM = unEventM

asksEventEnv :: forall x a. HasSpiderTimeline x => (EventEnv x -> a) -> EventM x a
asksEventEnv f = return $ f $ _spiderTimeline_eventEnv (unSTE (spiderTimeline :: SpiderTimelineEnv x))

class MonadIO m => Defer a m where
  getDeferralQueue :: m (IORef [a])

{-# INLINE defer #-}
defer :: Defer a m => a -> m ()
defer a = do
  q <- getDeferralQueue
  liftIO $ modifyIORef' q (a:)

instance HasSpiderTimeline x => Defer (SomeAssignment x) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvAssignments

instance HasSpiderTimeline x => Defer (SomeHoldInit x) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvHoldInits

instance Defer (SomeHoldInit x) (BehaviorM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = BehaviorM $ asks snd

instance HasSpiderTimeline x => Defer (SomeMergeUpdate x) (EventM x) where
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

putCurrentHeight :: HasSpiderTimeline x => Height -> EventM x ()
putCurrentHeight h = do
  heightRef <- asksEventEnv eventEnvCurrentHeight
  liftIO $ writeIORef heightRef $! h

instance HasSpiderTimeline x => Defer (Some Clear) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvClears

{-# INLINE scheduleClear #-}
scheduleClear :: Defer (Some Clear) m => IORef (Maybe a) -> m ()
scheduleClear r = defer $ Some $ Clear r

{-# INLINE writeAndScheduleClear #-}
writeAndScheduleClear :: Defer (Some Clear) m => IORef (Maybe a) -> a -> m ()
writeAndScheduleClear ref val = do
  liftIO $ writeIORef ref (Just val)
  scheduleClear ref

{-# INLINE writeAndScheduleIntClear #-}
writeAndScheduleIntClear :: Defer (Some IntClear) m => IORef (IntMap a) -> IntMap a -> m ()
writeAndScheduleIntClear ref val = do
  liftIO $ writeIORef ref val
  scheduleIntClear ref


instance HasSpiderTimeline x => Defer (Some IntClear) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvIntClears

{-# INLINE scheduleIntClear #-}
scheduleIntClear :: Defer (Some IntClear) m => IORef (IntMap a) -> m ()
scheduleIntClear r = defer $ Some $ IntClear r

instance HasSpiderTimeline x => Defer (Some RootClear) (EventM x) where
  {-# INLINE getDeferralQueue #-}
  getDeferralQueue = asksEventEnv eventEnvRootClears

{-# INLINE scheduleRootClear #-}
scheduleRootClear :: Defer (Some RootClear) m => IORef (DMap k Identity) -> m ()
scheduleRootClear r = defer $ Some $ RootClear r

-- Note: hold cannot examine its event until after the phase is over
{-# INLINE [1] hold #-}
hold :: forall p x m. (HasSpiderTimeline x, Patch p, Defer (SomeHoldInit x) m) => PatchTarget p -> Event x p -> m (Hold x p)
hold v0 e = do
  valRef <- liftIO $ newIORef v0
  invsRef <- liftIO $ newIORef [] -- invalidators
  parentRef <- liftIO $ newIORef Nothing
#ifdef DEBUG_NODEIDS
  nodeId <- liftIO newNodeId
#endif
  defer $ SomeHoldInit $ do
      ep <- liftIO $ readIORef $ parentRef
      case ep of
        Just _subd -> pure ()
        Nothing -> do
          subscriptionRef <- liftIO $ newIORef $ error "getHoldEventSubscription: subdRef uninitialized"
          (subscription@(EventSubscription _ _), occ) <- subscribeAndRead e $ Subscriber
             { subscriberPropagate = {-# SCC "traverseHold" #-} \a -> do
                {-# SCC "trace" #-} when debugPropagate $ traceM (Proxy :: Proxy x) $ liftIO $ do
                  invalidators <- liftIO $ readIORef $ invsRef
                  return $ "SubscriberHold" <> showNodeId' nodeId <> ": " ++ show (length invalidators)
              
                v <- {-# SCC "read" #-} liftIO $ readIORef $ valRef
                case {-# SCC "apply" #-} apply a v of
                  Nothing -> return ()
                  Just v' -> do
                    {-# SCC "trace2" #-} withIncreasedDepth (Proxy :: Proxy x) $
                      tracePropagate (Proxy :: Proxy x) ("propagateSubscriberHold: assigning Hold" <> showNodeId' nodeId)
                    vRef <- {-# SCC "vRef" #-} liftIO $ evaluate $ valRef
                    iRef <- {-# SCC "iRef" #-} liftIO $ evaluate $ invsRef
                    defer $ {-# SCC "assignment" #-} SomeAssignment vRef iRef v'
             , subscriberInvalidateHeight = \_ -> return ()
             , subscriberRecalculateHeight = \_ -> return ()
             }
          liftIO $ writeIORef subscriptionRef $! subscription
          case occ of
            Nothing -> return ()
            Just o -> do
              old <- liftIO $ readIORef $ valRef
              case apply o old of
                Nothing -> return ()
                Just new -> do
                  -- Need to evaluate these so that we don't retain the Hold itself
                  v <- liftIO $ evaluate $ valRef
                  i <- liftIO $ evaluate $ invsRef
                  defer $ SomeAssignment v i new
          liftIO $ writeIORef parentRef $ Just subscription
  return $ Hold
        { holdValue = valRef
        , holdInvalidators = invsRef
        , holdEvent = e
        , holdParent = parentRef
        }

type BehaviorEnv x = (Maybe (Weak (Invalidator x), IORef [SomeBehaviorSubscribed x]), IORef [SomeHoldInit x])

-- BehaviorM can sample behaviors
newtype BehaviorM x a = BehaviorM { unBehaviorM :: ReaderIO (BehaviorEnv x) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadReader (BehaviorEnv x))

data BehaviorSubscribed x a
   = forall p. BehaviorSubscribedHold (Hold x p)
   | BehaviorSubscribedPull (PullSubscribed x a)

newtype SomeBehaviorSubscribed x = SomeBehaviorSubscribed (Some (BehaviorSubscribed x))

-- type role PullSubscribed representational nominal

data Invalidator x
   = InvalidatorPull (IO ())
   | InvalidatorSwitch (IO ())

newtype SomeHoldInit x = SomeHoldInit (EventM x ())

data SomeMergeUpdate x = SomeMergeUpdate
  { _someMergeUpdate_invalidateHeight :: !(IO ())
  , _someMergeUpdate_recalculateHeight :: !(IO ())
  , _someMergeUpdate_update :: !(EventM x [EventSubscription x])
  }

newtype SomeInit x = SomeInit { unSomeInit :: EventM x () }

-- EventM can do everything BehaviorM can, plus create holds
newtype EventM x a = EventM { unEventM :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadException, MonadAsyncException, MonadCatch, MonadThrow, MonadMask)

data HeightBag = HeightBag
  { _heightBag_size :: {-# UNPACK #-} !Int
  , _heightBag_contents :: !(IntMap Word) -- Number of excess in each bucket
  }
  deriving (Show, Read, Eq, Ord)

heightBagEmpty :: HeightBag
heightBagEmpty = heightBagVerify $ HeightBag 0 IntMap.empty

heightBagSize :: HeightBag -> Int
heightBagSize = _heightBag_size

heightBagFromList :: [Height] -> HeightBag
heightBagFromList heights = heightBagVerify $ foldl' (flip heightBagAdd) heightBagEmpty heights

heightBagAdd :: Height -> HeightBag -> HeightBag
heightBagAdd (Height h) (HeightBag s c) = heightBagVerify $ HeightBag (succ s) $
  IntMap.insertWithKey (\_ _ old -> succ old) h 0 c

heightBagRemove :: Height -> HeightBag -> HeightBag
heightBagRemove (Height h) b@(HeightBag s c) = heightBagVerify $ case IntMap.lookup h c of
  Nothing -> error $ "heightBagRemove: Height " <> show h <> " not present in bag " <> show b
  Just old -> HeightBag (pred s) $ case old of
    0 -> IntMap.delete h c
    _ -> IntMap.insert h (pred old) c

heightBagRemoveMaybe :: Height -> HeightBag -> Maybe HeightBag
heightBagRemoveMaybe (Height h) (HeightBag s c) = heightBagVerify . removed <$> IntMap.lookup h c where
  removed old = HeightBag (pred s) $ case old of
    0 -> IntMap.delete h c
    _ -> IntMap.insert h (pred old) c

heightBagMax :: HeightBag -> Height
heightBagMax (HeightBag _ c) = case IntMap.maxViewWithKey c of
  Just ((h, _), _) -> Height h
  Nothing -> zeroHeight

heightBagVerify :: HeightBag -> HeightBag
#ifdef DEBUG
heightBagVerify b@(HeightBag s c) = if
  | s /= IntMap.size c + fromIntegral (sum (IntMap.elems c))
    -> error $ "heightBagVerify: size doesn't match: " <> show b
  | unHeight invalidHeight `IntMap.member` c
    -> error $ "heightBagVerify: contains invalid height: " <> show b
  | otherwise -> b
#else
heightBagVerify = id
#endif

data DynType x p = UnsafeDyn !(BehaviorM x (PatchTarget p), Event x p)
                 | BuildDyn  !(EventM x (PatchTarget p), Event x p)
                 | HoldDyn   !(Hold x p)

newtype Dyn (x :: Type) p = Dyn { unDyn :: IORef (DynType x p) }

newMapDyn :: _ => (a -> b) -> DynamicS x (Identity a) -> DynamicS x (Identity b)
newMapDyn f d = dynamicDynIdentity $ unsafeBuildDynamic (fmap f $ readBehaviorTracked $ dynamicCurrent d) (Identity . f . runIdentity <$> dynamicUpdated d)

buildDynamic :: forall x m p. (HasSpiderTimeline x, Defer (SomeHoldInit x) m, Patch p) => EventM x (PatchTarget p) -> Event x p -> m (Dyn x p)
buildDynamic readV0 v' = do
  result <- liftIO $ newIORef $ BuildDyn (readV0, v')
  let !d = Dyn result
  defer $ SomeHoldInit @x $ void $ getDynHold d
  return d

unsafeBuildDynamic :: BehaviorM x (PatchTarget p) -> Event x p -> Dyn x p
unsafeBuildDynamic readV0 v' =
  Dyn $ unsafePerformIO $ newIORef $ UnsafeDyn (readV0, v')

instance HasSpiderTimeline x => Functor (Event x) where
  fmap f = push $ return . Just . f

instance HasSpiderTimeline x => Functor (Behavior x) where
  fmap f = pull . fmap f . readBehaviorTracked

{-# INLINE push #-}
push :: HasSpiderTimeline x => (a -> EventM x (Maybe b)) -> Event x a -> Event x b
push f e = cacheEvent (pushCheap f e)


-- TODO: what is really needed here?
data PullSubscribed x a
   = PullSubscribed { pullSubscribedValue :: !a
                    , pullSubscribedInvalidators :: !(IORef [Weak (Invalidator x)])
                    , pullSubscribedOwnInvalidator :: !(Invalidator x)
                    , pullSubscribedParents :: ![SomeBehaviorSubscribed x] -- Need to keep parent behaviors alive, or they won't let us know when they're invalidated
                    }

{-# INLINABLE pull #-}
pull :: Defer (SomeMergeUpdate x) (EventM x) => BehaviorM x a -> Behavior x a
pull a = unsafePerformIO $ do
  ref <- newIORef Nothing
  invsRef <- newIORef $ error "pull: invsRef uninitialized"
#ifdef DEBUG_NODEIDS
  nodeId <- newNodeId
#endif
  let i = InvalidatorPull $ do
            traceInvalidate $ "invalidate: Pull" <> showNodeId' nodeId
            mVal <- readIORef $ ref
            forM_ mVal $ \_val -> do
              writeIORef ref Nothing
              evaluate =<< invalidate invsRef
  pure $ Behavior $ do
    subscribed <- liftIO (readIORef ref) >>= \case
      Just subscribed -> do
        askInvalidator >>= mapM_ (\wi -> liftIO $ modifyIORef' invsRef (wi:))
        liftIO $ touch $ i
        return $ subscribed
      Nothing -> do
        wi <- liftIO $ mkWeakPtrWithDebug i "InvalidatorPull"
        parentsRef <- liftIO $ newIORef []
        (_, !holdInits) <- ask -- ask behavior hold inits
        aVal <- liftIO $ runReaderIO (unBehaviorM a) (Just (wi, parentsRef), holdInits)
        liftIO . writeIORef invsRef . maybeToList =<< askInvalidator
        parents <- liftIO $ readIORef parentsRef
        let subscribed = PullSubscribed
              { pullSubscribedValue = aVal
              , pullSubscribedInvalidators = invsRef
              , pullSubscribedOwnInvalidator = i
              , pullSubscribedParents = parents
              }
        liftIO $ writeIORef ref $ Just subscribed
        return subscribed
    addParentB (BehaviorSubscribedPull subscribed)
    pure $ pullSubscribedValue subscribed

{-# INLINE commonEvent #-}
commonEvent :: forall x extra a. HasSpiderTimeline x =>
  IO () ->
  IO [EventSubscribed x] ->
  ((forall a1. String -> ((a -> EventM x ()) -> a1 -> EventM x ()) -> Subscriber x a1)
   -> IORef Height
   -> Subscriber x a
   -> EventM x (Maybe a, Height, extra)) ->
  Subscriber x a ->
  EventM x (EventSubscription x, Maybe a)
commonEvent cleanupSpecific eventSubscribedGetParents_ foo sub = do
  heightRef <- liftIO $ newIORef $ error "commonEvent: heightRef uninitialized"
  toRetainRef <- liftIO $ newIORef $ error "commonEvent: toRetainRef uninitialized"
  (occ, height, toRetainSpecific) <-
    foo
    -- newSubscriber:
    (\debugName propagateSpecific -> debugSubscriber' debugName $
        Subscriber
          { subscriberPropagate = propagateSpecific $ subscriberPropagate sub
          , subscriberInvalidateHeight = \_height ->
              invalidateHeightRef heightRef (subscriberInvalidateHeight sub) -- TODO: what normally happens with the passed in height here?
          , subscriberRecalculateHeight = updateCommonHeight heightRef sub
          })
    heightRef
    sub
  liftIO $ writeIORef heightRef height
  liftIO $ writeIORef toRetainRef $ (sub, toRetainSpecific) -- TODO: is toRetain correct?
  pure ( EventSubscription
          (cleanupSpecific >> writeIORef toRetainRef (error "commonEvent: toRetainRef uninitialized after unsubscribe"))
          (EventSubscribed
            { eventSubscribedHeightRef = heightRef
            , eventSubscribedRetained = toAny toRetainRef
#ifdef DEBUG_CYCLES
            , eventSubscribedGetParents = eventSubscribedGetParents_
            , eventSubscribedHasOwnHeightRef = True
            , eventSubscribedWhoCreated = whoCreatedIORef heightRef
#endif
            })
       , occ
       )

-- TODO: Slow, but terminates and doesn't exhibit growing memory when not cached (but memory use is huge).
{-# INLINABLE switch #-}
switch :: forall x a. _ => Behavior x (Event x a) -> Event x a
switch switchParent = cacheEvent $ Event $ \sub -> do
  -- TODO: This should be unnecessary, because it will always be filled with just the single parent behavior:
  -- Adriaan: I think this is because only readBehaviorTracked is run so its argument is the only parent
  --          that will be put in parentsRef. However you'd have to parameterize over "setting parents"
  --          in Behavior to fix that TODO?
  parentsRef :: IORef [SomeBehaviorSubscribed x] <- liftIO $ newIORef []
  currentParentSubscriptionRef <- liftIO $ newIORef $ error "switch: currentParentSubscriptionRef uninitialized"
  ownWeakInvalidatorRef <- liftIO $ newIORef $ error "switch: ownWeakInvalidatorRef uninitialized"
  commonEvent
    (do unsubscribe =<< readIORef currentParentSubscriptionRef
        finalize =<< readIORef ownWeakInvalidatorRef) -- We don't need to get invalidated if we're dead
    (do s <- readIORef currentParentSubscriptionRef
        return [_eventSubscription_subscribed s])
    (\newSubscriber heightRef sub -> do
        let subscriber = newSubscriber "SubscriberSwitch" id
        ownInvalidator <- mfix $ \i -> liftIO $ evaluate $ InvalidatorSwitch $  -- traceInvalidate $ "invalidate: Switch" <> showNodeId subscribed           
         runEventM @x $ defer $ SomeMergeUpdate @x
          ({-# SCC "switchSubscribed" #-} do
            EventSubscription _ subd' <- readIORef currentParentSubscriptionRef
            parentHeight <- getEventSubscribedHeight subd'
            myHeight <- readIORef heightRef
            when (parentHeight /= myHeight) $ do
              writeIORef heightRef $! invalidHeight
              invalidateSubscriberHeight myHeight sub)
          (updateCommonHeight heightRef sub
            =<< getEventSubscribedHeight . _eventSubscription_subscribed
            =<< readIORef currentParentSubscriptionRef)
          ({-# SCC "switchSubscribed" #-} liftIO $ do
            oldSubscription <- readIORef currentParentSubscriptionRef
            wi <- readIORef ownWeakInvalidatorRef
            traceInvalidate $ "Finalizing invalidator for Switch" -- TODO: <> showNodeId subscribedCommon
            finalize wi
            wi' <- mkWeakPtrWithDebug i "wi'"
            writeIORef ownWeakInvalidatorRef $! wi'
            writeIORef parentsRef []
            -- FIXME: why is this wonky? Can we do better than reusing runHoldInits in this way?
            holdInitsRef <- newIORef []
            -- TODO: after this runBehavior holdInitsRef always seems empty...
            e <- runBehaviorM (readBehaviorTracked switchParent) (Just (wi', parentsRef)) $ holdInitsRef
            runEventM $ runHoldInits holdInitsRef =<< liftIO (newIORef [])
            --TODO: Make sure we touch the pieces of the SwitchSubscribed at the appropriate times
            subscription <- unSpiderHost . runFrame . subscribe e $ {-# SCC "subscribeSwitch" #-} subscriber --TODO: Assert that the event isn't firing --TODO: This should not loop because none of the events should be firing, but still, it is inefficient
            writeIORef currentParentSubscriptionRef $! subscription
            return [oldSubscription])
        wi <- liftIO $ mkWeakPtrWithDebug ownInvalidator "InvalidatorSwitch"
        holdInits <- getDeferralQueue
        (subscription, height, parentOcc) <-
          join $ subscribeAndReadWithHeight
          <$> liftIO (runBehaviorM (readBehaviorTracked switchParent) (Just (wi, parentsRef)) holdInits)
          <*> pure subscriber
        liftIO $ writeIORef ownWeakInvalidatorRef wi
        liftIO $ writeIORef currentParentSubscriptionRef subscription
        pure (parentOcc, height, (ownInvalidator, ownWeakInvalidatorRef, currentParentSubscriptionRef)))
    sub


-- TODO: calculateSwitchHeight and calculateCoincidenceHeight are similar in that they both take the
--     currentParent/outerParent height, and coincidence also the inner height. The result is the maximum
--     of all used heights.
-- TODO: coincidenceSubscribedOuterParent seems to appear in similar places as switchSubscribedCurrentParent
-- FIXME: semantics test-suite uses huge and growing amounts of memory (and possibly doesn't terminate) when coincidence isn't cached
coincidence :: forall x a. (HasSpiderTimeline x) => Event x (Event x a) -> Event x a
coincidence coincidenceParent = cacheEvent $ Event $ \sub -> do
  innerSubdRef <- liftIO $ newIORef $ error "coincidence: innerSubdRef undefined"
  outerParentSubscriptionRef <- liftIO $ newIORef $ error "coincidence : outerParentSubscriptionRef undefined"
  occRef :: IORef (Maybe a) <- liftIO $ newIORef Nothing
  -- TODO: switch returns currentParent which is ~ outerParent, coincidence also returns innerParent
  let getParentSubscribeds = do
        maybeInnerSubscription <- readIORef innerSubdRef
        outerSubscription <- readIORef outerParentSubscriptionRef
        return $ _eventSubscription_subscribed outerSubscription : maybeToList maybeInnerSubscription
  commonEvent
    (unsubscribe =<< readIORef outerParentSubscriptionRef) -- TODO: switch does the same but also finalizes OwnWeakInvalidator
    getParentSubscribeds
    (\newSubscriber heightRef sub -> do
        let subscribeCoincidenceInner :: Event x a -> Height -> EventM x (Maybe a, Height)
            subscribeCoincidenceInner inner outerHeight = do
              (subscription@(EventSubscription _ innerSubd), innerHeight, innerOcc) <-
                subscribeAndReadWithHeight inner $ newSubscriber "SubscriberCoincidenceInner" $ \doPropagate a -> do
                     occ <- liftIO $ readIORef occRef
                     case occ of
                       Just _ -> return () -- SubscriberCoincidenceOuter must have already propagated this event
                       Nothing -> do
                         writeAndScheduleClear occRef a
                         doPropagate a
              writeAndScheduleClear innerSubdRef innerSubd
              let innerHeightWasHigher = innerHeight > outerHeight
              defer $ SomeMergeUpdate @x
                 (do unsubscribe subscription
                     when innerHeightWasHigher $
                       invalidateHeightRef heightRef (subscriberInvalidateHeight sub))
                 (when innerHeightWasHigher $
                   updateCommonHeight heightRef sub =<< do
                     subs <- mapM getEventSubscribedHeight =<< getParentSubscribeds
                     -- TODO: why not order heights with invalid as Top?
                     return $ if invalidHeight `elem` subs then invalidHeight else maximum subs)
                 (pure [])
              return (innerOcc, max innerHeight outerHeight)
        (outerSubscription, outerHeight, outerOcc) <- subscribeAndReadWithHeight coincidenceParent $
          newSubscriber "SubscriberCoincidenceOuter" $ \doPropagate a ->
            {-# SCC "traverseCoincidenceOuter" #-} do
               outerHeight <- liftIO $ readIORef heightRef
               -- tracePropagate (Proxy :: Proxy x) $ "  outerHeight = " <> show outerHeight
               (occ, innerHeight) <- subscribeCoincidenceInner a outerHeight
               -- tracePropagate (Proxy :: Proxy x) $ "  isJust occ = " <> show (isJust occ)
               -- tracePropagate (Proxy :: Proxy x) $ "  innerHeight = " <> show innerHeight
               case occ of
                 Nothing ->
                   when (innerHeight > outerHeight) $ liftIO $ do -- If the event fires, it will fire at a later height
                     writeIORef heightRef $! innerHeight
                     invalidateSubscriberHeight outerHeight sub
                     recalculateSubscriberHeight innerHeight sub
                 Just o -> doPropagate o -- Since it's already firing, no need to adjust height
        liftIO $ writeIORef outerParentSubscriptionRef outerSubscription
        (occ, height) <- case outerOcc of
          Nothing -> return (Nothing, outerHeight)
          Just o -> subscribeCoincidenceInner o outerHeight
        mapM_ (writeAndScheduleClear occRef) occ
        pure (occ, height, (outerParentSubscriptionRef, innerSubdRef)))
    sub

-- Propagate the given event occurrence; before cleaning up, run the given action, which may read the state of events and behaviors
run :: forall x b. HasSpiderTimeline x => [DSum (RootTrigger x) Identity] -> EventM x b -> SpiderHost x b
run roots after = do
  tracePropagate (Proxy :: Proxy x) $ "Running an event frame with " <> show (length roots) <> " events"
  let t = spiderTimeline :: SpiderTimelineEnv x
  result <- SpiderHost $ withMVar (_spiderTimeline_lock (unSTE t)) $ \_ -> unSpiderHost $ runFrame $ do
    rootsToPropagate <- forM roots $ \r@(RootTrigger (_, occRef, k) :=> a) -> do
      occBefore <- liftIO $ do
        occBefore <- readIORef occRef
        writeIORef occRef $! DMap.insert k a occBefore
        return occBefore
      if DMap.null occBefore
        then do scheduleRootClear occRef
                return $ Just r
        else return Nothing
    forM_ (catMaybes rootsToPropagate) $ \(RootTrigger (subscribersRef, _, _) :=> Identity a) -> do
      propagate a subscribersRef
    delayedRef <- asksEventEnv eventEnvDelayedMerges
    let go = do
          delayed <- liftIO $ readIORef delayedRef
          case IntMap.minViewWithKey delayed of
            Nothing -> return ()
            Just ((currentHeight, cur), future) -> do
              tracePropagate (Proxy :: Proxy x) $ "Running height " ++ show currentHeight
              putCurrentHeight $ Height currentHeight
              liftIO $ writeIORef delayedRef $! future
              sequence_ cur
              go
    go
    putCurrentHeight maxBound
    after
  tracePropagate (Proxy :: Proxy x) "Done running an event frame"
  return result

newtype Clear a = Clear (IORef (Maybe a))

newtype IntClear a = IntClear (IORef (IntMap a))

newtype RootClear k = RootClear (IORef (DMap k Identity))

data SomeAssignment x = forall a. SomeAssignment {-# UNPACK #-} !(IORef a) {-# UNPACK #-} !(IORef [Weak (Invalidator x)]) a

debugFinalize :: Bool
debugFinalize = False

mkWeakPtrWithDebug :: a -> String -> IO (Weak a)
mkWeakPtrWithDebug x debugNote = do
  x' <- evaluate x
  mkWeakPtr x' $
    if debugFinalize
    then Just $ debugStrLn $ "finalizing: " ++ debugNote
    else Nothing

type CanTrace x m = (HasSpiderTimeline x, MonadIO m)


#ifdef DEBUG

debugSubscriber' :: forall x a. HasSpiderTimeline x => String -> Subscriber x a -> Subscriber x a
debugSubscriber' description subscribed = Subscriber
  {
    subscriberPropagate = \m -> do
      tracePropagate (Proxy :: Proxy x) ("subscriberPropagate: " <> description)
      subscriberPropagate subscribed m
  , subscriberInvalidateHeight = \old -> do
      traceInvalidateHeight $ "invalidateSubscriberHeight: " <> description <> ", old = " <> show (unHeight old)
      subscriberInvalidateHeight subscribed old
      traceInvalidateHeight $ "invalidateSubscriberHeight: " <> description <> ", done"
  , subscriberRecalculateHeight = \new -> do
      traceInvalidateHeight $ "subscriberRecalculateHeight: " <> description <> ", new = " <> show (unHeight new)
      subscriberRecalculateHeight subscribed new
      traceInvalidateHeight $ "subscriberRecalculateHeight: " <> description <> ", done"
  }


{-# INLINE withIncreasedDepth #-}
withIncreasedDepth :: forall proxy x m a. CanTrace x m => proxy x -> m a -> m a
withIncreasedDepth _ a = do
  liftIO $ modifyIORef' (_spiderTimeline_depth $ unSTE (spiderTimeline :: SpiderTimelineEnv x)) succ
  result <- a
  liftIO $ modifyIORef' (_spiderTimeline_depth $ unSTE (spiderTimeline :: SpiderTimelineEnv x)) pred
  return result

{-# INLINE tracePropagate #-}
tracePropagate :: (CanTrace x m) => proxy x -> String -> m ()
tracePropagate p = when debugPropagate . trace p

{-# INLINE traceInvalidate #-}
traceInvalidate :: String -> IO ()
traceInvalidate = when debugInvalidate . liftIO . debugStrLn

{-# INLINE traceInvalidateHeight #-}
traceInvalidateHeight :: String -> IO ()
traceInvalidateHeight = when debugInvalidateHeight . liftIO . debugStrLn

{-# INLINE trace #-}
trace :: (CanTrace x m) => proxy x ->  String -> m ()
trace p message = traceM p $ return message

{-# INLINE traceM #-}
traceM :: forall x proxy m. (CanTrace x m) => proxy x -> m String -> m ()
traceM _ getMessage = do
  message <- getMessage
  d <- liftIO $ readIORef $ _spiderTimeline_depth $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  liftIO $ debugStrLn $ replicate d ' ' <> message

#else

{-# INLINE withIncreasedDepth #-}
withIncreasedDepth ::  proxy x -> m a -> m a
withIncreasedDepth _ = id

{-# INLINE tracePropagate #-}
tracePropagate :: (CanTrace x m) => proxy x -> String -> m ()
tracePropagate _ _ = return ()

{-# INLINE traceInvalidate #-}
traceInvalidate :: String -> IO ()
traceInvalidate _ = return ()

{-# INLINE traceInvalidateHeight #-}
traceInvalidateHeight :: String -> IO ()
traceInvalidateHeight _ = return ()

{-# INLINE debugSubscriber' #-}
debugSubscriber' :: String -> Subscriber x a -> Subscriber x a
debugSubscriber' _ = id

{-# INLINE trace #-}
trace :: (CanTrace x m) => proxy x ->  String -> m ()
trace _ _ = return ()

{-# INLINE traceM #-}
traceM :: (CanTrace x m) => proxy x -> m String -> m ()
traceM _ _ = return ()

#endif

whoCreatedIORef :: IORef a -> IO [String]
whoCreatedIORef (IORef a) = whoCreated $! a

groupByHead :: Eq a => [NonEmpty a] -> [(a, NonEmpty [a])]
groupByHead = \case
  [] -> []
  (x :| xs) : t -> case groupByHead t of
    [] -> [(x, xs :| [])]
    l@((y, yss) : t')
      | x == y -> (x, xs `NonEmpty.cons` yss) : t'
      | otherwise -> (x, xs :| []) : l

listsToForest :: Eq a => [[a]] -> Forest a
listsToForest lists = buildForest <$> groupByHead (mapMaybe nonEmpty lists)
    where buildForest (a, lists') = Node a $ listsToForest $ toList lists'

showStacks :: [[String]] -> String
showStacks = drawForest . listsToForest . fmap (filterStack "Reflex.Spider.Internal")

filterStack :: String -> [String] -> [String]
#ifdef DEBUG_HIDE_INTERNALS
filterStack prefix = filter (not . (prefix `isPrefixOf`))
#else
filterStack _prefix = id
#endif

#ifdef DEBUG_CYCLES

data EventLoopException = EventLoopException [[String]]
instance Exception EventLoopException

instance Show EventLoopException where
  show (EventLoopException stacks) = "causality loop detected:\n" <> if null stacks
    then "no location information, compile with profiling enabled for stack tree"
    else showStacks stacks

#else

data EventLoopException = EventLoopException
instance Exception EventLoopException

instance Show EventLoopException where
  show EventLoopException = "causality loop detected: \n" <>
    "compile reflex with flag 'debug-cycles' and compile with profiling enabled for stack tree"

#endif


runBehaviorM :: BehaviorM x a -> Maybe (Weak (Invalidator x), IORef [SomeBehaviorSubscribed x]) -> IORef [SomeHoldInit x] -> IO a
runBehaviorM a mwi holdInits = runReaderIO (unBehaviorM a) (mwi, holdInits)

askInvalidator :: BehaviorM x (Maybe (Weak (Invalidator x)))
askInvalidator = do
  (!m, _) <- ask
  case m of
    Nothing -> return Nothing
    Just (!wi, _) -> return $ Just wi

-- TODO: What is the meaning of this function?
addParentB :: BehaviorSubscribed x a -> BehaviorM x ()
addParentB h = do
  (!m, _) <- ask
  case m of
    Nothing -> pure ()
    Just (_, !p) ->
      liftIO $ modifyIORef' p (SomeBehaviorSubscribed (Some h) :)

{-# INLINE getDynHold #-}
getDynHold :: (HasSpiderTimeline x, Defer (SomeHoldInit x) m, Patch p) => Dyn x p -> m (Hold x p)
getDynHold d = do
  mh <- liftIO $ readIORef $ unDyn d
  case mh of
    HoldDyn h -> return h
    UnsafeDyn (readV0, v') -> do
      holdInits <- getDeferralQueue
      v0 <- liftIO $ runBehaviorM readV0 Nothing holdInits
      hold' v0 v'
    BuildDyn (readV0, v') -> do
      v0 <- liftIO $ runEventM readV0
      hold' v0 v'
  where
    hold' v0 v' = do
      h <- hold v0 v'
      liftIO $ writeIORef (unDyn d) $ HoldDyn h
      return h


-- Always refers to 0
{-# NOINLINE zeroRef #-}
zeroRef :: IORef Height
zeroRef = unsafePerformIO $ newIORef zeroHeight


newtype EventSelector x k = EventSelector { select :: forall a. k a -> Event x a }
newtype EventSelectorG x k v = EventSelectorG { selectG :: forall a. k a -> Event x (v a) }

newtype FanSubscribedChildren x k v a = FanSubscribedChildren
  { _fanSubscribedChildren :: WeakBag (Subscriber x (v a))
  }

fanG :: forall x k v. (HasSpiderTimeline x, GCompare k) => Event x (DMap k v) -> EventSelectorG x k v
fanG e = unsafePerformIO $ do
  -- TODO: no need for Maybe in parentSubscriptionRef? Can do things unsafely instead
  -- This is the subscription which will update occRef:
  subscribersRef :: IORef (DMap k (FanSubscribedChildren x k v)) <- newIORef DMap.empty
  parentSubscriptionRef :: (IORef (EventSubscription x)) <- newIORef $ error "fanG: no subscription"
  occRef :: IORef (Maybe (DMap k v)) <- newIORef Nothing
#ifdef DEBUG_NODEIDS
  nodeId <- liftIO $ newNodeId
#endif
  pure $ EventSelectorG $ \(!k) -> Event $ \sub -> do
    whenM (liftIO $ DMap.null <$> readIORef subscribersRef) $ do
      -- Not initialized: subscribe to parent.
      (subscription, parentOcc) <- subscribeAndRead e $ debugSubscriber' ("SubscriberFan " <> showNodeId' nodeId) $ Subscriber
        { subscriberPropagate = \a -> {-# SCC "traverseFan" #-} do
            subs <- liftIO $ readIORef subscribersRef
            tracePropagate (Proxy :: Proxy x) $
                    show (DMap.size subs) <> " keys subscribed, " <> show (DMap.size a) <> " keys firing"
            writeAndScheduleClear occRef a
            _ <- DMap.traverseWithKey (\_ (Pair v subsubs) -> do
                                          propagate v $ _fanSubscribedChildren subsubs
                                          return $ Constant ())
                 $ DMap.intersectionWithKey (const Pair) a subs --TODO: Would be nice to have DMap.traverse_
            return ()
        , subscriberInvalidateHeight = \old -> do
            subscribers <- readIORef subscribersRef
            forM_ (DMap.toList subscribers) $ \(_ :=> v) ->
              WeakBag.traverse_ (_fanSubscribedChildren v) $ invalidateSubscriberHeight old
        , subscriberRecalculateHeight = \new -> do
            subscribers <- readIORef subscribersRef
            forM_ (DMap.toList subscribers) $ \(_ :=> v) ->
              WeakBag.traverse_ (_fanSubscribedChildren v) $ recalculateSubscriberHeight new
        }
      liftIO $ writeIORef parentSubscriptionRef $ subscription
      mapM_ (writeAndScheduleClear occRef) parentOcc
    liftIO $ do
      sln <- do
        subscribers <- readIORef subscribersRef
        list <- case DMap.lookup k subscribers of
          -- No WeakBag of subscribers yet for this key:
          Nothing -> {-# SCC "missSubscribeFanSubscribed" #-} do
            list <- WeakBag.empty
            writeIORef subscribersRef $! DMap.insert k (FanSubscribedChildren list) subscribers
            pure list
          Just (FanSubscribedChildren list) -> {-# SCC "hitSubscribeFanSubscribed" #-} pure list
        WeakBag.insert' sub list $ do -- called when the WeakBag for a key is empty:
          reducedSubscribers <- DMap.delete k <$> readIORef subscribersRef
          writeIORef subscribersRef $! reducedSubscribers
          -- When we don't have any subscribers, unsubscribe from e
          when (DMap.null reducedSubscribers) $ do
            unsubscribe =<< readIORef parentSubscriptionRef
            writeIORef parentSubscriptionRef (error "fanG: parentSubscriptionRef emptied")
      subscribedParent <- liftIO $ _eventSubscription_subscribed <$> readIORef parentSubscriptionRef
      ( EventSubscription
              (WeakBag.remove sln >> touch sln)
              (EventSubscribed
               { eventSubscribedHeightRef = eventSubscribedHeightRef subscribedParent
               , eventSubscribedRetained = toAny (sln, parentSubscriptionRef)
#ifdef DEBUG_CYCLES
               , eventSubscribedGetParents = return [subscribedParent]
               , eventSubscribedHasOwnHeightRef = False
               , eventSubscribedWhoCreated = whoCreatedIORef $ parentSubscriptionRef
#endif
               })
            ,)
        <$> ((DMap.lookup k =<<) <$> liftIO (readIORef occRef))

newtype EventSelectorInt x a = EventSelectorInt { selectInt :: Int -> Event x a }

fanInt :: HasSpiderTimeline x => Event x (IntMap a) -> EventSelectorInt x a
fanInt p = unsafePerformIO $ do
  subscribers <- FastMutableIntMap.newEmpty --TODO: Clean up the keys in here when their child weak bags get empty --TODO: Remove our own subscription when the subscribers list is completely empty
  subscriptionRef <- newIORef $ error "fanInt: no subscription"
  occRef <- newIORef mempty
#ifdef DEBUG_NODEIDS
  nodeId <- newNodeId
#endif
  pure $ EventSelectorInt $ \k -> Event $ \sub -> do
    isEmpty <- liftIO $ FastMutableIntMap.isEmpty subscribers
    when isEmpty $ do -- This is the first subscriber, so we need to subscribe to our input
      let desc = "fanInt" <> showNodeId' nodeId <> ", k = "  <> show k
      (subscription, parentOcc) <- subscribeAndRead p $ debugSubscriber' desc $ Subscriber
        { subscriberPropagate = \m -> do
            -- TODO: this is like writeAndScheduleClearAndPropagate
            writeAndScheduleIntClear occRef m
            FastMutableIntMap.forIntersectionWithImmutable_ subscribers m $ \b v ->  --TODO: Do we need to know that no subscribers are being added as we traverse?
              propagateFast v b
        , subscriberInvalidateHeight = \old ->
            FastMutableIntMap.for_ subscribers $ \b ->
              FastWeakBag.traverse_ b $ \s ->
                subscriberInvalidateHeight s old
        , subscriberRecalculateHeight = \new ->
            FastMutableIntMap.for_ subscribers $ \b ->
              FastWeakBag.traverse_ b $ \s ->
                subscriberRecalculateHeight s new
        }
      liftIO $ writeIORef subscriptionRef subscription
      mapM_ (writeAndScheduleIntClear occRef) parentOcc
    liftIO $ do
      b <- FastMutableIntMap.lookup subscribers k >>= \case
        Nothing -> do
          b <- FastWeakBag.empty
          FastMutableIntMap.insert subscribers k b
          return b
        Just b -> return b
      ticket <- liftIO $ FastWeakBag.insert sub b
      currentOcc <- readIORef occRef
      subscribed <- do
        subscribedParent <- _eventSubscription_subscribed <$> readIORef subscriptionRef
        return $ EventSubscribed
          { eventSubscribedHeightRef = eventSubscribedHeightRef subscribedParent
          , eventSubscribedRetained = toAny (subscriptionRef, ticket)
#ifdef DEBUG_CYCLES
          , eventSubscribedGetParents = return [subscribedParent]
          , eventSubscribedHasOwnHeightRef = False
          , eventSubscribedWhoCreated = whoCreatedIORef subscriptionRef
#endif
          }
      return (EventSubscription (FastWeakBag.remove ticket) subscribed, IntMap.lookup k currentOcc)

mergeInt :: forall x a. (HasSpiderTimeline x) => DynamicS x (PatchIntMap (Event x a)) -> Event x (IntMap a)
mergeInt =
  merge
  (\ipt tellE -> IntMap.traverseWithKey (\k v -> tellE (IntMap.singleton k <$> v)) ipt)
  (\(PatchIntMap ip) s tellE -> do
     ip' <- IntMap.traverseWithKey (\k ->mapM (tellE . fmap (IntMap.singleton k))) ip
     traverse_ fst $ IntMap.intersection s ip
     pure $ applyAlways (PatchIntMap ip') s)
  IntMap.null
  (fmap snd . IntMap.elems)
  IntMap.size

{-# INLINE mergeG' #-}
mergeG' :: forall k q x v patch. (HasSpiderTimeline x, GCompare k, PatchTarget (patch k q) ~ DMap k q)
  => ( patch k q
       -> DMap k (Constant (MergeM x (), EventSubscription x))
       -> TellE x (DMap k v)
       -> MergeM x (DMap k (Constant (MergeM x (), EventSubscription x))))
  -> (forall a. q a -> Event x (v a))
  -> DynamicS x (patch k q)
  -> Event x (DMap k v)
mergeG' doPatch nt =
  merge
  (\ipt tellE -> DMap.traverseWithKey (\k v -> Constant <$> tellE (DMap.singleton k <$> nt v)) ipt)
  doPatch
  DMap.null
  (fmap (\(_ :=> (Constant (_, sub))) -> sub) . DMap.toList)
  DMap.size

mergeG :: forall k q x v. (HasSpiderTimeline x, GCompare k)
  => (forall a. q a -> Event x (v a)) -> DynamicS x (PatchDMap k q) -> Event x (DMap k v)
mergeG nt =
  mergeG'
  (\ip s tellE -> do
     ip' <- traversePatchDMapWithKey (\k v -> Constant <$> tellE (DMap.singleton k <$> nt v))
            ip
     mapM_ (\(_ :=> v) -> fst $ getConstant v) . DMap.toList $ PatchDMap.getDeletions ip s
     pure $ applyAlways ip' s)
  nt

mergeWithMove :: forall k x v q. (HasSpiderTimeline x, GCompare k)
  => (forall a. q a -> Event x (v a)) -> DynamicS x (PatchDMapWithMove k q) -> Event x (DMap k v)
mergeWithMove nt =
  mergeG'
  (\ip s tellE -> do
     ip' <- traversePatchDMapWithMoveWithKey (\k v ->
                               Constant <$> tellE (DMap.singleton k <$> nt v))
            ip
     sequence_ $ mapMaybe (\(_ :=> v) -> getConstant v)
          $ DMap.toList
          $ DMap.intersectionWithKey
            (\_ to (Constant unsub) ->
                Constant $ case getComposeMaybe to of
                  Nothing -> -- We are deleting/replacing
                    Just (fst unsub)
                  Just _toKey -> do -- We are moving
                    Nothing)
            (DMap.map PatchDMapWithMove._nodeInfo_to . unPatchDMapWithMove $ ip')
            s
     pure $ applyAlways ip' s)
  nt

checkCycle :: HasSpiderTimeline x => EventSubscribed x -> EventM x ()
checkCycle subscribed = liftIO $ do
    height <- readIORef (eventSubscribedHeightRef subscribed)
    -- currentHeight <- getCurrentHeight
    -- when (height <= currentHeight) $ if height /= invalidHeight
    --     then do
    --       myStack <- liftIO $ whoCreatedIORef undefined --TODO
    --       error $ "Height (" ++ show height ++ ") is not greater than current height (" ++ show currentHeight ++ ")\n" ++ unlines (reverse myStack)
    --     else liftIO $
    when (height == invalidHeight) $
#ifdef DEBUG_CYCLES
          do
            nodesInvolvedInCycle <- walkInvalidHeightParents subscribed
            stacks <- forM nodesInvolvedInCycle whoCreatedEventSubscribed
            throwIO (EventLoopException stacks)
#else
          throwIO EventLoopException
#endif

type MergeM x a = WriterT [EventSubscription x] (EventM x) a
type TellE x a = Event x a -> MergeM x (MergeM x (), EventSubscription x)

{-# INLINE merge #-}
merge :: forall x ip ipt o s.
  ( HasSpiderTimeline x, PatchTarget ip ~ ipt, Monoid o, Monoid s)
  => (ipt -> TellE x o -> MergeM x s)
  -> (ip -> s -> TellE x o -> MergeM x s)
  -> (o -> Bool)
  -> (s -> [EventSubscription x])
  -> (s -> Int)
  -> DynamicS x ip -- p is the type of DMap Patch (i.e. With/Without Move)
  -> Event x o
merge doInitialInput doPatchInput outputIsEmpty getSubs getNumSubs d =
 cacheEvent $ Event $ \sub -> do
  -- TODO: is it worth caching the number of subscriptions?
  --      This is now done with 'getNumSubs' but those functions traverse a tree.
  accumRef :: IORef o <- liftIO $ newIORef $ mempty
  heightRef <- liftIO $ newIORef $ zeroHeight
  heightBagRef <- liftIO $ newIORef $ heightBagEmpty
  toRetainRef <- liftIO $ newIORef $ error "getMergeSubscribed: toRetainRef not yet initialized"
  stateRef <- liftIO $ newIORef $ error "merge state not initialized"
  let subscribed = EventSubscribed
        { eventSubscribedHeightRef = heightRef
        , eventSubscribedRetained = toAny toRetainRef
#ifdef DEBUG_CYCLES
        , eventSubscribedGetParents =
            fmap _eventSubscription_subscribed . getSubs <$> readIORef stateRef
        , eventSubscribedHasOwnHeightRef = False
        , eventSubscribedWhoCreated = whoCreatedIORef heightRef
#endif
        }
  let invalidateMyHeight = invalidateHeightRef heightRef (subscriberInvalidateHeight sub)
  let recalculateMyHeight = do
          currentHeight <- readIORef $ heightRef
          -- revalidateMergeHeight may be called multiple times; perhaps the's a way to finesse it to avoid this check
          -- TODO: This will almost always be true; can we get rid of this check and just proceed to the next one always?
          when (currentHeight == invalidHeight) $ do
            heights <- readIORef $ heightBagRef
            parentsCount <- getNumSubs <$> readIORef stateRef
            -- When the number of heights in the bag reaches the number of parents, we should have a valid height
            case heightBagSize heights `compare` parentsCount of
              LT -> return ()
              EQ -> do
                let height = succHeight $ heightBagMax heights
                traceInvalidateHeight $ "recalculateSubscriberHeight: height: " <> show height
                writeIORef heightRef $! height
                subscriberRecalculateHeight sub height
              GT -> error $ "revalidateMergeHeight: more heights (" <> show (heightBagSize heights) <> ") than parents (" <> show parentsCount <> ") for Merge"
  let {-# INLINE [1] mergeSubscribeAndRead #-}
      mergeSubscribeAndRead isInit e = do -- not isInit == isUpdate
        let addAccum !a = do
              oldAccum <- liftIO (readIORef accumRef)
              liftIO $ writeIORef accumRef $! (a <> oldAccum) -- left-biased generally but there shouldn't be dup'd keys
              when (outputIsEmpty oldAccum) $ do -- Only schedule the firing once
                checkCycle subscribed
                let scheduleMerge' initialHeight = do
                      scheduleMerge initialHeight $ do
                        height <- liftIO $ readIORef heightRef
                        currentHeight <- getCurrentHeight
                        case height `compare` currentHeight of
                          LT -> error "Somehow a merge's height has been decreased after it was scheduled"
                          -- The height has been increased (by a coincidence event;
                          -- TODO: is this the only way?)
                          GT -> scheduleMerge' height
                          EQ -> do
                            vals <- liftIO $ readIORef accumRef
                             -- TODO: this is an unfortunate effect of my
                             -- attempt to use addAccum both at init time and
                             -- update time.
                            unless (outputIsEmpty vals) $ do
                            -- Once we're done with this, we can clear it immediately, because if there's a cacheEvent in front of us,
                            -- it'll handle subsequent subscribers, and if not, we won't get subsequent subscribers
                              liftIO $ writeIORef accumRef $! mempty
                              subscriberPropagate sub vals
                scheduleMerge' <=< liftIO $ readIORef heightRef
        -- TODO: is "subscribeAndReadWithThisPropagation" something handy? Avoids defining having to define and use addAccum twice here, and it might lead to more consistency everywhere.
        (subscription@(EventSubscription _ parentSubd), parentOcc) <-
          lift $ subscribeAndRead e $ Subscriber
             { subscriberPropagate = addAccum
             , subscriberInvalidateHeight = \old -> do
                 --TODO: When removing a parent doesn't actually change the height, maybe we can avoid invalidating
                 modifyIORef' heightBagRef $ heightBagRemove old
                 invalidateMyHeight
             , subscriberRecalculateHeight = \new -> do
                 modifyIORef' heightBagRef $ heightBagAdd new
                 recalculateMyHeight
             }
        height <- liftIO $ getEventSubscribedHeight parentSubd
        -- TODO: Can isInit be avoided?
        lift $ mapM_ addAccum parentOcc
        liftIO $ if not isInit
          then modifyIORef' heightBagRef $ heightBagAdd height -- new parent height
          else do
            if height == invalidHeight
              then writeIORef heightRef invalidHeight
              else do
                modifyIORef' heightBagRef $ heightBagAdd height
                modifyIORef' heightRef $ \oldHeight ->
                  if oldHeight == invalidHeight
                  then invalidHeight
                  else max (succHeight height) oldHeight
        liftIO $ do
          pure . (, subscription) $ do
            liftIO $ modifyIORef' heightBagRef . heightBagRemove
                 <=< getEventSubscribedHeight . _eventSubscription_subscribed
                 $ subscription
            W.tell [subscription]
  subsToKillIllegal <- W.execWriterT $
    liftIO . writeIORef stateRef
    =<< flip doInitialInput (mergeSubscribeAndRead True)
    =<< lift (readBehaviorUntracked (dynamicCurrent d))
  unless (null subsToKillIllegal) $ error "Merge init function killed subscriptions, this shouldn't happen"
  defer $ SomeInit $ do
    let deferUpdateMerge p = do
          -- TODO: Be able to run as much of this as possible promptly
          defer $ SomeMergeUpdate invalidateMyHeight recalculateMyHeight $ do
            oldState <- liftIO $ readIORef stateRef
            W.execWriterT $ liftIO . writeIORef stateRef =<< doPatchInput p oldState (mergeSubscribeAndRead False)
    (changeSubscription, change) <- subscribeAndRead (dynamicUpdated d) $ Subscriber
          { subscriberPropagate = \a -> {-# SCC "traverseMergeChange" #-} do
              tracePropagate (Proxy :: Proxy x) "SubscriberMerge/Change"
              deferUpdateMerge a
          , subscriberInvalidateHeight = \_ -> return ()
          , subscriberRecalculateHeight = \_ -> return ()
          }
    forM_ change deferUpdateMerge
    -- We explicitly hold on to the unsubscribe function from subscribing to the update event.
    -- If we don't do this, there are certain cases where mergeCheap will fail to properly retain
    -- its subscription.
    liftIO $ writeIORef toRetainRef (changeSubscription, stateRef)
  fmap ( EventSubscription
           (do traverse_ unsubscribe . getSubs =<< readIORef stateRef
               writeIORef stateRef mempty) -- TOOD: needed/useful?
           subscribed
       , ) . runMaybeT $ do
       guard =<< lift ((>=) <$> getCurrentHeight <*> liftIO (readIORef heightRef)) -- If we should have fired by now
       dm <- liftIO $ readIORef accumRef
       guard (not (outputIsEmpty dm))
       liftIO $ writeIORef accumRef mempty
       pure dm

-- TODO: Getting rid of all these different types which get initialized at the same time anyway
--   might lead to patterns showing up in code.
runHoldInits :: forall x. HasSpiderTimeline x => IORef [SomeHoldInit x] -> IORef [SomeInit x] -> EventM x ()
runHoldInits holdInitRef initRef = do
  holdInits <- liftIO $ readIORef holdInitRef
  inits <- liftIO $ readIORef initRef
  unless (null holdInits && null inits) $ do
    liftIO $ writeIORef holdInitRef []
    liftIO $ writeIORef initRef []
    forM_ holdInits $ \(SomeHoldInit h) ->  h
    forM_ inits $ unSomeInit -- TODO: why is merge init just a thunk but do dyn/hold inits use a data type?
    runHoldInits holdInitRef initRef

newEventEnv :: IO (EventEnv x)
newEventEnv = do
  toAssignRef <- newIORef [] -- This should only actually get used when events are firing
  holdInitRef <- newIORef []
  mergeUpdateRef <- newIORef []
  initRef <- newIORef []
  heightRef <- newIORef zeroHeight
  toClearRef <- newIORef []
  toClearIntRef <- newIORef []
  toClearRootRef <- newIORef []
  delayedRef <- newIORef IntMap.empty
  return $ EventEnv toAssignRef holdInitRef mergeUpdateRef initRef toClearRef toClearIntRef toClearRootRef heightRef delayedRef

clearEventEnv :: EventEnv x -> IO ()
clearEventEnv (EventEnv toAssignRef holdInitRef mergeUpdateRef initRef toClearRef toClearIntRef toClearRootRef heightRef delayedRef) = do
  writeIORef toAssignRef []
  writeIORef holdInitRef []
  writeIORef mergeUpdateRef []
  writeIORef initRef []
  writeIORef heightRef zeroHeight
  writeIORef toClearRef []
  writeIORef toClearIntRef []
  writeIORef toClearRootRef []
  writeIORef delayedRef IntMap.empty


invalidate :: forall x. (Defer (SomeMergeUpdate x) (EventM x)) => IORef [Weak (Invalidator x)] -> IO ()
invalidate wisRef = do
  wis <- readIORef wisRef
  evaluate <=< forM_ wis $ \wi -> do
    mi <- deRefWeak wi
    case mi of
      Nothing -> void $ traceInvalidate "invalidate Dead" --TODO: Should we clean this up here?
      Just i -> do
        finalize wi -- Once something's invalidated, it doesn't need to hang around; this will change when some things are strict
        case i of
          InvalidatorPull p -> p
          InvalidatorSwitch someMergeUpdate -> someMergeUpdate
  writeIORef wisRef []

-- | Run an event action outside of a frame
runFrame :: forall x a. HasSpiderTimeline x => EventM x a -> SpiderHost x a --TODO: This function also needs to hold the mutex
runFrame a = SpiderHost $ do
  let env = _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  result <- runEventM $ do
        result <- a
        runHoldInits (eventEnvHoldInits env) (eventEnvInits env) -- This must happen before doing the assignments, in case subscribing a Hold causes existing Holds to be read by the newly-propagated events
        return result
  toClear <- readIORef $ eventEnvClears env
  forM_ toClear $ \(Some (Clear ref)) -> {-# SCC "clear" #-} writeIORef ref Nothing
  toClearInt <- readIORef $ eventEnvIntClears env
  forM_ toClearInt $ \(Some (IntClear ref)) -> {-# SCC "intClear" #-} writeIORef ref $! IntMap.empty
  toClearRoot <- readIORef $ eventEnvRootClears env
  forM_ toClearRoot $ \(Some (RootClear ref)) -> {-# SCC "rootClear" #-} writeIORef ref $! DMap.empty
  toAssign <- readIORef $ eventEnvAssignments env
  forM_ toAssign $ \(SomeAssignment vRef iRef v) -> {-# SCC "assignment" #-} do
    writeIORef vRef v
    traceInvalidate $ "Invalidating Hold"
    -- TODO: explain what invalidate does:
    --TODO: There are some things that will need to be re-subscribed every time; we should try to avoid finalizing them.
    -- TODO: Invalidate used to return an empty list, this might have been in anticipation to the TODO above.
    invalidate iRef
  mergeUpdates <- readIORef (eventEnvMergeUpdates env)
  clearEventEnv env
  tracePropagate (Proxy::Proxy x) $ "Updating merges"
  mergeSubscriptionsToKill <- runEventM $ concat <$> mapM _someMergeUpdate_update mergeUpdates
  tracePropagate (Proxy::Proxy x) $ "Updating merges done"
  liftIO $ mapM_ unsubscribe mergeSubscriptionsToKill
  mapM_ _someMergeUpdate_invalidateHeight mergeUpdates --TODO: In addition to when the patch is completely empty, we should also not run this if it has some Nothing values, but none of them have actually had any effect; potentially, we could even check for Just values with no effect (e.g. by comparing their IORefs and ignoring them if they are unchanged); actually, we could just check if the new height is different
  mapM_ _someMergeUpdate_recalculateHeight mergeUpdates
  return result

newtype Height = Height { unHeight :: Int } deriving (Show, Read, Eq, Ord, Bounded)

{-# INLINE zeroHeight #-}
zeroHeight :: Height
zeroHeight = Height 0

{-# INLINE invalidHeight #-}
invalidHeight :: Height
invalidHeight = Height (-1000)

#ifdef DEBUG_CYCLES
-- | An invalid height that is currently being traversed, e.g. by walkInvalidHeightParents
{-# INLINE invalidHeightBeingTraversed #-}
invalidHeightBeingTraversed :: Height
invalidHeightBeingTraversed = Height (-1001)
#endif

-- Only used in merge
{-# INLINE succHeight #-}
succHeight :: Height -> Height
succHeight h@(Height a) =
  if h == invalidHeight
  then invalidHeight
  else Height $ succ a

-- TODO: what should this function be called?
invalidateHeightRef :: IORef Height -> (Height -> IO ()) -> IO ()
invalidateHeightRef heightRef doOnInvalidate = do
  oldHeight <- readIORef heightRef
  -- Don't do anything if the height is already invalid
  when (oldHeight /= invalidHeight) $ do
    writeIORef heightRef $! invalidHeight
    doOnInvalidate oldHeight

-- TODO: comments say that 'when's should be assertions but tests fail if they are removed
updateCommonHeight :: IORef Height -> Subscriber x a -> Height -> IO ()
updateCommonHeight heightRef subscriber newHeight = do
  oldHeight <- readIORef heightRef
  when (oldHeight == invalidHeight) $ do --TODO: This 'when' should probably be an assertion
    when (newHeight /= invalidHeight) $ do --TODO: This 'when' should probably be an assertion
      writeIORef heightRef $! newHeight
      recalculateSubscriberHeight newHeight subscriber

unsafeNewSpiderTimelineEnv :: forall x. IO (SpiderTimelineEnv x)
unsafeNewSpiderTimelineEnv = do
  lock <- newMVar ()
  env <- newEventEnv
#ifdef DEBUG
  depthRef <- newIORef 0
#endif
  return $ STE $ SpiderTimelineEnv
    { _spiderTimeline_lock = lock
    , _spiderTimeline_eventEnv = env
#ifdef DEBUG
    , _spiderTimeline_depth = depthRef
#endif
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

newtype SpiderPullM (x :: Type) a = SpiderPullM (BehaviorM x a) deriving (Functor, Applicative, Monad, MonadIO, MonadFix)

newtype SpiderPushM (x :: Type) a = SpiderPushM (EventM x a) deriving (Functor, Applicative, Monad, MonadIO, MonadFix)

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
  {-# INLINABLE (>>) #-}
  SpiderHost x >> SpiderHost y = SpiderHost $ x >> y
  {-# INLINABLE return #-}
  return x = SpiderHost $ return x
#if !MIN_VERSION_base(4,13,0)
  {-# INLINABLE fail #-}
  fail = MonadFail.fail
#endif

data NewFanSubscribedChildren x a = NewFanSubscribedChildren
  { _newFanSubscribedChildren :: WeakBag (Subscriber x a)
  , _newFanSubscribedUninit :: IO ()
  }

-- TODO: anything in common with Fan?
newFanEventWithTriggerIO :: forall x k. (HasSpiderTimeline x, GCompare k) => (forall a. k a -> RootTrigger x a -> IO (IO ())) -> IO (EventSelector x k)
newFanEventWithTriggerIO f = do
  occRef <- newIORef DMap.empty
  subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  return $ EventSelector $ \(!k) -> Event $ \sub -> liftIO $ do
    (NewFanSubscribedChildren subscribers uninit) <- DMap.lookup k <$> readIORef subscribedRef >>= \case
      Just res -> {-# SCC "hitRoot" #-} pure res
      Nothing -> {-# SCC "missRoot" #-} do
        subscribers <- WeakBag.empty
        uninit <- f k $ RootTrigger (subscribers, occRef, k)
        let res = NewFanSubscribedChildren subscribers uninit
        modifyIORef' subscribedRef $ DMap.insertWith (error $ "getRootSubscribed: duplicate key inserted into Root") k res
        pure res
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
    occ <- fmap (coerce . DMap.lookup k) $ readIORef $ occRef
    return ( EventSubscription
             (WeakBag.remove sln >> touch sln)
             EventSubscribed
             { eventSubscribedHeightRef = zeroRef
             , eventSubscribedRetained = toAny subscribedRef
#ifdef DEBUG_CYCLES
             , eventSubscribedGetParents = return []
             , eventSubscribedHasOwnHeightRef = False
             , eventSubscribedWhoCreated = return ["root"]
#endif
             }             
           , occ
           )
