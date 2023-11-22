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



{-# OPTIONS_GHC -Wunused-binds #-}
{-# LANGUAGE PartialTypeSignatures #-}

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
    withSpiderTimeline,
    EventLoopException(..)) where

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
import Unsafe.Coerce
import Data.Reflection
import Data.Some (Some(Some))
import Control.Monad.Reader
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Text.Printf (printf)
import Witherable (filter)
import Prelude hiding (filter)
-- import Debug.RecoverRTTI (anythingToString)

anythingToString :: p -> String
anythingToString _ = "<anythingToString>"


type WeakBag a = IORef (IntMap a)

wbEmpty :: IO (WeakBag a)
wbEmpty = newIORef mempty

wbInsert :: a -> IORef (IntMap a) -> IO (IntMap.Key, WeakBag a)
wbInsert a wb = do
  as <- readIORef wb
  let i = maybe 0 (succ . fst . fst) . IntMap.maxViewWithKey $ as
  writeIORef wb (IntMap.insert i a as)
  pure (i,wb)

wbRemove :: (IntMap.Key, WeakBag a) -> IO ()
wbRemove (i,wb) = modifyIORef wb $ IntMap.delete i

{-# NOINLINE nodeCtrRef #-}
nodeCtrRef :: IORef Int
nodeCtrRef = unsafePerformIO $ newIORef (0 :: Int)

newNodeId :: (MonadIO m) => m Int
newNodeId = liftIO $ atomicModifyIORef nodeCtrRef (\n -> (succ n, n))

type Weak a = IORef (Maybe a)

finalize :: Weak a -> IO ()
finalize w = writeIORef w Nothing

newtype EventSubscription x = EventSubscription { unsubscribe :: IO () }
newtype Subscriber x a = Subscriber { subscriberPropagate :: Maybe a -> EventM x () }

returnSubscription :: Monad m => IO () -> Maybe (Maybe b) -> m (EventSubscription x, Maybe (Maybe b))
returnSubscription cleanup occ = return (EventSubscription cleanup, occ)

subscribeWithRec :: R.Event (SpiderTimeline x) a -> (EventSubscription x -> Maybe a -> EventM x (Maybe b)) -> Subscriber x b -> EventM x (EventSubscription x, Maybe (Maybe b))
subscribeWithRec e f subscriber = mdo
  (subscription, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate subscriber <=< (subscription `f`)
  fmap (subscription,) .  mapM (subscription `f`) $ occ

-- | Propagate everything
propagate :: forall x a. Maybe a -> WeakBag (Subscriber x a) -> EventM x ()
propagate a subscribers =
  (\ f -> traverse_ f <=< liftIO . readIORef $ subscribers) $ \s -> subscriberPropagate s a

-- | Stores all global data relevant to a particular Spider timeline; only one
-- value should exist for each type @x@
newtype SpiderTimelineEnv (x :: Type) = STE {unSTE :: SpiderTimelineEnv' x}
-- We implement SpiderTimelineEnv with a newtype wrapper so
-- we can get the coercions we want safely.
data SpiderTimelineEnv' x = SpiderTimelineEnv
  { _spiderTimeline_lock :: MVar ()
  , _spiderTimeline_eventEnv :: EventEnv x
  , _spiderTimeline_rootEvent :: Subscriber x () -> EventM x (EventSubscription x, Maybe (Maybe ()))
  , _spiderTimeline_triggerRootEvent :: IO ()
  , _spiderTimeline_rootTriggers :: IORef (IntMap (Some (RootTrigger x)))
  }

data EventEnv x
   = EventEnv { eventEnvAssignments :: IORef [SomeAssignment x] -- Needed for Subscribe  -- This should only actually get used when events are firing
              , eventEnvInits :: IORef [EventM x ()] -- Needed for Subscribe
              , eventEnvClears :: IORef [IO ()] -- Needed for Subscribe
              , eventEnvBla :: IORef [IO ()]
              }

asksEventEnv :: forall x a. HasSpiderTimeline x => (EventEnv x -> a) -> EventM x a
asksEventEnv f = return $ f $ _spiderTimeline_eventEnv (unSTE (spiderTimeline :: SpiderTimelineEnv x))

addToQueue :: MonadIO m => a -> IORef [a] -> m ()
addToQueue a q = liftIO $ modifyIORef' q (a:)

deferClear :: forall x. HasSpiderTimeline x => IO () -> EventM x ()
deferClear thunk = addToQueue thunk =<< asksEventEnv eventEnvClears

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
run triggers after = do
  let t = spiderTimeline :: SpiderTimelineEnv x
  liftIO $ putStrLn "\nRUN ~~~"
  SpiderHost $ withMVar (_spiderTimeline_lock (unSTE t)) $ \_ -> unSpiderHost $ runFrame $ do
    liftIO $ putStrLn "RUNNING"
    forM_ triggers $ \(RootTrigger trigger :=> Identity a) -> do
      liftIO $ printf "trigger with value: %s\n" $ anythingToString a
      liftIO $ trigger a
    liftIO (_spiderTimeline_triggerRootEvent (unSTE t))
    after

data SomeAssignment x = forall a. SomeAssignment (IORef a) (IORef [Weak Invalidator]) a

-- | Run an event action outside of a frame
runFrame :: forall x a. HasSpiderTimeline x => EventM x a -> SpiderHost x a --TODO: This function also needs to hold the mutex
runFrame a = SpiderHost $ do
  liftIO $ putStrLn "-- START RUNFRAME"
  let (EventEnv toAssignRef initRef toClearRef toBlaRef) =
        _spiderTimeline_eventEnv $ unSTE (spiderTimeline :: SpiderTimelineEnv x)
  result <- runEventM a
  -- This must happen before doing the assignments, in case subscribing a Hold causes existing Holds to be read by the newly-propagated events:
  liftIO $ putStr "INITS"
  fix $ \runHoldInits' -> do
    inits <- readIORef initRef
    unless (null inits) $ do
      writeIORef initRef []
      runEventM $ mapM_ (\m -> liftIO (putStr ".") >> m) inits
      runHoldInits'
  liftIO $ putStrLn "\nCLEARS"
  atomicModifyIORef toClearRef ([],) >>= sequence_
  liftIO $ putStrLn "ASSIGNMENTS"
  atomicModifyIORef toAssignRef ([],)
    >>= mapM_ (\(SomeAssignment vRef iRef v) -> do
                  writeIORef vRef v
                  mapM_ (\wi -> maybe (pure ()) (\i -> finalize wi >> i) <=< readIORef $ wi)
                      =<< readIORef iRef
                  writeIORef iRef [])
  liftIO $ putStrLn "BLAS"
  atomicModifyIORef toBlaRef ([],) >>= sequence_
  return result

unsafeNewSpiderTimelineEnv :: forall x. IO (SpiderTimelineEnv x)
unsafeNewSpiderTimelineEnv = do
  lock <- newMVar ()
  env <- do toAssignRef <- newIORef []
            initRef <- newIORef []
            toClearRef <- newIORef []
            toBlaRef <- newIORef []
            return $ EventEnv toAssignRef initRef toClearRef toBlaRef
  triggers <- newIORef mempty
  rootSubscribers :: WeakBag (Subscriber x a) <- wbEmpty
  rootOccRef :: IORef (Maybe (Maybe ())) <- newIORef Nothing
  return $ STE $ SpiderTimelineEnv
    { _spiderTimeline_lock = lock
    , _spiderTimeline_eventEnv = env
    , _spiderTimeline_rootEvent = \sub -> do
        sln <- liftIO $ wbInsert sub rootSubscribers
        occ <- liftIO $ readIORef rootOccRef
        returnSubscription (wbRemove sln) occ
    , _spiderTimeline_triggerRootEvent = runEventM @x $ do
        liftIO $ writeIORef rootOccRef (Just (Just ()))
        liftIO $ printf "propagating rootEvent\n"
        propagate (Just ()) rootSubscribers
        addToQueue (writeIORef rootOccRef Nothing) (eventEnvClears env)
    , _spiderTimeline_rootTriggers = triggers
    }

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (EventM x) where
  sample b = liftIO . runBehaviorM b Nothing =<< asksEventEnv eventEnvInits

data BehaviorEnv x = BehaviorEnv
  { behaviorEnvMaybeWISubs :: Maybe (Weak Invalidator)
  , _behaviorEnvInitsRef :: IORef [EventM x ()]
  }

type Invalidator = IO ()

runBehaviorM :: _ -> Maybe (Weak Invalidator) -> IORef [EventM x ()] -> IO a
runBehaviorM (Behavior a) mwi holdInits = runReaderIO a (BehaviorEnv mwi holdInits)

rootEvent :: forall x. HasSpiderTimeline x => R.Event (SpiderTimeline x) ()
rootEvent = Event (_spiderTimeline_rootEvent (unSTE (spiderTimeline :: SpiderTimelineEnv x)))

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (EventM x) where
  -- Note: cannot examine its event until after the phase is over
  buildHold readV0 e = do
    invsRef <- liftIO $ newIORef [] -- invalidators
    valRef <- liftIO . unsafeInterleaveIO $ newIORef =<< runEventM @x readV0
    addToQueue (do void $ liftIO $ evaluate valRef
                   void $ subscribeWithRec e
                     (const (mapM (\a -> do
                                    addToQueue (SomeAssignment @x valRef invsRef a) =<< asksEventEnv eventEnvAssignments
                                    pure Nothing)))
                     $ Subscriber (const (pure ())))
      =<< asksEventEnv eventEnvInits
    pure $ Behavior $ do
      asks behaviorEnvMaybeWISubs >>= mapM_ (liftIO . modifyIORef' invsRef . (:))
      liftIO $ readIORef valRef

  now = R.headE rootEvent

instance HasSpiderTimeline x => R.Reflex (SpiderTimeline x) where
  {-# SPECIALIZE instance R.Reflex (SpiderTimeline Global) #-}
  newtype Behavior (SpiderTimeline x) a = Behavior { readBehaviorTracked :: BehaviorM x a }
  newtype Event (SpiderTimeline x) a = Event { subscribeAndRead :: Subscriber x a -> EventM x (EventSubscription x, Maybe (Maybe a)) }
  type PullM (SpiderTimeline x) = BehaviorM x
  type PushM (SpiderTimeline x) = EventM x

  never = error "never value got evaluated??" <$ filter (const False) rootEvent

  cacheEvent :: forall a. R.Event (SpiderTimeline x) a -> R.Event (SpiderTimeline x) a
  cacheEvent e = unsafePerformIO $ do
    liftIO $ putStrLn "cacheEvent being subscribed to"
    subscribers :: WeakBag (Subscriber x a) <- wbEmpty
    occRef <- liftIO $ newIORef Nothing
    void . runEventM @x . subscribeWithRec e (\_ occ -> writeAndScheduleClear "cacheEvent" occRef occ >> pure occ)
           $ Subscriber { subscriberPropagate = flip propagate subscribers }
    pure $ Event $ \sub -> do
      liftIO $ printf "cacheEvent occ on read: %s\n" . anythingToString =<< readIORef occRef
      sln <- liftIO $ wbInsert sub subscribers
      returnSubscription (wbRemove sln) <=< liftIO $ readIORef occRef

  pushCheap :: (a -> R.PushM (SpiderTimeline x) (Maybe b)) -> R.Event (SpiderTimeline x) a -> R.Event (SpiderTimeline x) b
  pushCheap f e = Event $ subscribeWithRec e (\_ -> fmap join . mapM f)

  pull :: R.PullM (SpiderTimeline x) a -> R.Behavior (SpiderTimeline x) a
  pull = Behavior

  switchUncached :: R.Behavior (SpiderTimeline x) (R.Event (SpiderTimeline x) a) -> R.Event (SpiderTimeline x) a
  switchUncached switchParent = Event $ \sub ->
    -- TODO: eventEnvInits is always empty?
    fix $ \f -> mfix $ \(~(subscription,_occ)) -> do
      wi <- liftIO . newIORef . Just . addToQueue (unsubscribe subscription >> void (runEventM @x f)) =<< asksEventEnv eventEnvBla
      e <- liftIO . runBehaviorM (R.sample switchParent) (Just wi) =<< asksEventEnv eventEnvInits
      (parentSubscription, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate sub
      returnSubscription (finalize wi >> unsubscribe parentSubscription) occ

  coincidenceUncached :: R.Event (SpiderTimeline x) (R.Event (SpiderTimeline x) a) -> R.Event (SpiderTimeline x) a
  coincidenceUncached coincidenceParent = Event $ \sub -> do
    let f = fmap join
          . mapM (maybe
                  (pure (Just Nothing))
                  (\innerE -> mdo
                      fmap snd .
                        subscribeWithRec innerE (\subscriptionInner occ -> do
                                                    liftIO (unsubscribe subscriptionInner)
                                                    pure occ)
                        $ Subscriber $ subscriberPropagate sub))
    (subscriptionOuter, occOuter) <-
      subscribeAndRead coincidenceParent $ Subscriber $ mapM_ (subscriberPropagate sub) <=< f . Just
    occ <- f occOuter
    returnSubscription (unsubscribe subscriptionOuter) occ

  unsafeBuildIncremental :: R.PullM (SpiderTimeline x) (R.PatchTarget p) -> R.Event (SpiderTimeline x) p -> R.Incremental (SpiderTimeline x) p
  unsafeBuildIncremental = R.Incremental . R.pull

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
    liftIO $ printf "merge occ on subscription: %s\n" $ anythingToString maybeOcc
    returnSubscription (mapM_ (unsubscribe . snd) =<< readIORef occRefsSubscriptionsRef) maybeOcc

  eventCoercion Coercion = Coercion

  behaviorCoercion Coercion = Coercion


newtype NewFanSubscribedChildren x a = NewFanSubscribedChildren
  { _newFanSubscribedChildren :: WeakBag (Subscriber x a)
  }

newtype RootTrigger x a = RootTrigger (a -> IO ())

newFanEventWithTriggerIO :: forall x k. (GCompare k, HasSpiderTimeline x) => (forall a. k a -> RootTrigger x a -> IO (IO ())) -> IO (R.EventSelector (SpiderTimeline x) k)
newFanEventWithTriggerIO f = do
  nodeId <- newNodeId
  subscribedRef :: IORef (DMap k (NewFanSubscribedChildren x)) <- newIORef DMap.empty
  occRef <- newIORef DMap.empty
  return $ R.EventSelector $ \k ->
    Event $ \sub -> do
      (NewFanSubscribedChildren subscribers) <- liftIO $
        (\case
            Just res -> pure res
            Nothing -> do
              subscribers <- wbEmpty
              _uninit <- f k $ RootTrigger $ \a -> do
                printf "trigger %d adding value: %s\n"  nodeId $ anythingToString a
                occBefore <- readIORef occRef
                when (DMap.null occBefore) $
                  runEventM @x $ deferClear $ writeIORef occRef DMap.empty
                modifyIORef occRef $ DMap.insert k (Identity a)
              (_subscription, _) <- runEventM @x $ subscribeAndRead rootEvent $ Subscriber $ \_ -> do
                occ <- fmap runIdentity . DMap.lookup k <$> liftIO (readIORef occRef)
                liftIO $ printf "propagating trigger %d to subscribers: %s\n" nodeId $ anythingToString occ
                propagate occ subscribers
              let res = NewFanSubscribedChildren subscribers
              modifyIORef' subscribedRef $ DMap.insertWith (error "getRootSubscribed: duplicate key inserted into Root") k res
              pure res)
        . DMap.lookup k
        =<< readIORef subscribedRef
      sln <- liftIO $ wbInsert sub subscribers
      (rootSubscription, maybeOccRoot) <- subscribeAndRead rootEvent $ Subscriber $ const (pure ())
      occ <- case maybeOccRoot of
        Nothing -> pure Nothing
        Just _ -> Just . fmap runIdentity . DMap.lookup k <$> liftIO (readIORef occRef)
      liftIO $ unsubscribe rootSubscription -- TODO: just give access to rootOccRef
      returnSubscription (wbRemove sln) -- TODO: unsubscribe parent if empty
        occ







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

data SpiderEventHandle x a = SpiderEventHandle
  { spiderEventHandleSubscription :: EventSubscription x
  , spiderEventHandleValue :: IORef (Maybe a)
  }

-- | The monad for actions that manipulate a Spider timeline identified by @x@
newtype SpiderHost (x :: Type) a = SpiderHost { unSpiderHost :: IO a } deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadFail)

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (SpiderHost x) where
  buildHold getV0 e = runFrame . runSpiderHostFrame $ Reflex.Class.buildHold getV0 e
  now = runFrame . runSpiderHostFrame $ Reflex.Class.now

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (SpiderHost x) where
  sample = runFrame . R.sample

instance HasSpiderTimeline x => Reflex.Class.MonadSample (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  sample = Reflex.Spider.Internal.ReadPhase . Reflex.Class.sample

instance HasSpiderTimeline x => Reflex.Class.MonadHold (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  buildHold getV0 e = Reflex.Spider.Internal.ReadPhase $ Reflex.Class.buildHold getV0 e
  now = Reflex.Spider.Internal.ReadPhase Reflex.Class.now

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHostFrame x) where
  subscribeEvent e = SpiderHostFrame $ do
    --TODO: Unsubscribe eventually (manually and/or with weak ref)
    valRef <- liftIO $ newIORef Nothing
    (subscription, _) <- subscribeWithRec e (\_ occ -> do
                                                mapM_ (writeAndScheduleClear "subscribeEvent" valRef) occ
                                                pure Nothing)
                         $ Subscriber (const (pure ()))
    return $ SpiderEventHandle
      { spiderEventHandleSubscription = subscription
      , spiderEventHandleValue = valRef
      }

instance HasSpiderTimeline x => Reflex.Host.Class.ReflexHost (SpiderTimeline x) where
  type EventTrigger (SpiderTimeline x) = RootTrigger x
  type EventHandle (SpiderTimeline x) = SpiderEventHandle x
  type HostFrame (SpiderTimeline x) = SpiderHostFrame x

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReadEvent (SpiderTimeline x) (Reflex.Spider.Internal.ReadPhase x) where
  readEvent h = Reflex.Spider.Internal.ReadPhase $ fmap (fmap return) $ liftIO $ do
    result <- readIORef $ spiderEventHandleValue h
    touch h
    return result

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHost x) where
  newFanEventWithTrigger f = SpiderHost $ newFanEventWithTriggerIO f

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexCreateTrigger (SpiderTimeline x) (SpiderHostFrame x) where
  newFanEventWithTrigger f = SpiderHostFrame $ EventM $ liftIO $ newFanEventWithTriggerIO f

instance HasSpiderTimeline x => Reflex.Host.Class.MonadSubscribeEvent (SpiderTimeline x) (SpiderHost x) where
  subscribeEvent = runFrame . runSpiderHostFrame . Reflex.Host.Class.subscribeEvent

instance HasSpiderTimeline x => Reflex.Host.Class.MonadReflexHost (SpiderTimeline x) (SpiderHost x) where
  type ReadPhase (SpiderHost x) = Reflex.Spider.Internal.ReadPhase x
  fireEventsAndRead es (Reflex.Spider.Internal.ReadPhase a) = run es a
  runHostFrame = runFrame . runSpiderHostFrame

instance MonadRef (EventM x) where
  type Ref (EventM x) = Ref IO
  newRef = liftIO . newRef
  readRef = liftIO . readRef
  writeRef r a = liftIO $ writeRef r a

instance MonadAtomicRef (EventM x) where
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
  deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadException, MonadAsyncException, MonadMask, MonadThrow, MonadCatch, R.MonadSample (SpiderTimeline x), R.MonadHold (SpiderTimeline x))

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
