{-|
Module: Reflex.BehaviorWriter.Base
Description: Implementation of BehaviorWriter
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.BehaviorWriter.Base
  ( BehaviorWriterT (..)
  , runBehaviorWriterT
  , withBehaviorWriterT
  , mapBehaviorWriterT
  ) where

import Control.Monad.Exception
import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Morph
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State.Strict

import Reflex.Class
import Reflex.Adjustable.Class
import Reflex.BehaviorWriter.Class
import Reflex.Host.Class
import Reflex.PerformEvent.Class
import Reflex.PostBuild.Class
import Reflex.Query.Class
import Reflex.Requester.Class
import Reflex.TriggerEvent.Class

-- TODO: The below is just cut, pasted, and renamed between Dynamic/Event/BehaviorWriter implementations.

import Control.Monad.Writer.Class
import Reflex.Writer.Base
import Data.Coerce (coerce)

-- | A basic implementation of 'BehaviorWriter'.
newtype BehaviorWriterT t w m a = BehaviorWriterT { unBehaviorWriterT :: ReflexWriterT w Behavior t m a }
  -- The list is kept in reverse order
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadTrans
    , MFunctor
    , MonadIO
    , MonadFix
    , MonadAsyncException
    , MonadException
    , MonadRef
    , MonadAtomicRef
    , MonadSample t
    , MonadHold t
    , MonadReflexCreateTrigger t
    , MonadReader r
    , PostBuild t
    )

-- | Run a 'BehaviorWriterT' action.  The dynamic writer output will be provided
-- along with the result of the action.
runBehaviorWriterT :: (MonadFix m, Reflex t, Monoid w) => BehaviorWriterT t w m a -> m (a, Behavior t w)
runBehaviorWriterT = runReflexWriterT . unBehaviorWriterT

instance (Adjustable t m, Monoid w, MonadHold t m, MonadFix m) => Adjustable t (BehaviorWriterT t w m) where
  runWithReplace v0 = BehaviorWriterT . runWithReplace (coerce v0) . fmap coerce
  traverseIntMapWithKeyWithAdjust f m e = BehaviorWriterT $ traverseIntMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjust f m e = BehaviorWriterT $ traverseDMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjustWithMove f m e = BehaviorWriterT $ traverseDMapWithKeyWithAdjustWithMove (\k v -> coerce (f k v)) m (fmap coerce e)


instance (Monad m, Monoid w, Reflex t) => BehaviorWriter t w (BehaviorWriterT t w m) where
  tellBehavior w = BehaviorWriterT $ tell w

-- TODO: Implement this using MonadTransControl.
-- | Map a function over the output of a 'BehaviorWriterT'.
withBehaviorWriterT :: (Monoid w, Monoid w', Reflex t, MonadHold t m)
                   => (w -> w')
                   -> BehaviorWriterT t w m a
                   -> BehaviorWriterT t w' m a
withBehaviorWriterT f (BehaviorWriterT dw) = BehaviorWriterT (withReflexWriterT f dw)

-- | Change the monad underlying an BehaviorWriterT
mapBehaviorWriterT
  :: (forall x. m x -> n x)
  -> BehaviorWriterT t w m a
  -> BehaviorWriterT t w n a
mapBehaviorWriterT f (BehaviorWriterT a) = BehaviorWriterT $ mapReflexWriterT f a

-- TODO: Automate all these implementations
instance PerformEvent t m => PerformEvent t (BehaviorWriterT t w m) where
  type Performable (BehaviorWriterT t w m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent = lift . performEvent

instance TriggerEvent t m => TriggerEvent t (BehaviorWriterT t w m) where
  newTriggerEvent = lift newTriggerEvent
  newTriggerEventWithOnComplete = lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete = lift . newEventWithLazyTriggerWithOnComplete

instance MonadState s m => MonadState s (BehaviorWriterT t w m) where
  get = lift get
  put = lift . put

instance Requester t m => Requester t (BehaviorWriterT t w m) where
  type Request (BehaviorWriterT t w m) = Request m
  type Response (BehaviorWriterT t w m) = Response m
  requesting = lift . requesting
  requesting_ = lift . requesting_

instance (MonadQuery t q m, Monad m) => MonadQuery t q (BehaviorWriterT t w m) where
  tellQueryIncremental = lift . tellQueryIncremental
  askQueryResult = lift askQueryResult
  queryIncremental = lift . queryIncremental
