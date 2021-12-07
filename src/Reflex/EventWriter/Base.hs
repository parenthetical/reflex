-- | This module provides 'EventWriterT', the standard implementation of
-- 'EventWriter'.
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.EventWriter.Base
  ( EventWriterT (..)
  , runEventWriterT
  , mapEventWriterT
  , withEventWriterT
  ) where

import Reflex.Adjustable.Class
import Reflex.Class
import Reflex.EventWriter.Class (EventWriter, tellEvent)
import Reflex.DynamicWriter.Class (DynamicWriter, tellDyn)
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

-- TODO: The below is just cut, pasted, and renamed between Dynamic/Event/BehaviorWriter implementations.

import Control.Monad.Writer.Class
import Reflex.Writer.Base
import Data.Coerce (coerce)

-- | A basic implementation of 'EventWriter'.
newtype EventWriterT t w m a = EventWriterT { unEventWriterT :: ReflexWriterT w Event t m a }
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

-- | Run a 'EventWriterT' action.  The dynamic writer output will be provided
-- along with the result of the action.
runEventWriterT :: (MonadFix m, Reflex t, Monoid w) => EventWriterT t w m a -> m (a, Event t w)
runEventWriterT = runReflexWriterT . unEventWriterT

instance (Adjustable t m, Monoid w, MonadHold t m, MonadFix m) => Adjustable t (EventWriterT t w m) where
  runWithReplace v0 = EventWriterT . runWithReplace (coerce v0) . fmap coerce
  traverseIntMapWithKeyWithAdjust f m e = EventWriterT $ traverseIntMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjust f m e = EventWriterT $ traverseDMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjustWithMove f m e = EventWriterT $ traverseDMapWithKeyWithAdjustWithMove (\k v -> coerce (f k v)) m (fmap coerce e)


instance (Monad m, Monoid w, Reflex t) => EventWriter t w (EventWriterT t w m) where
  tellEvent w = EventWriterT $ tell w


-- TODO: Implement this using MonadTransControl.
-- | Map a function over the output of a 'EventWriterT'.
withEventWriterT :: (Monoid w, Monoid w', Reflex t, MonadHold t m)
                   => (w -> w')
                   -> EventWriterT t w m a
                   -> EventWriterT t w' m a
withEventWriterT f (EventWriterT dw) = EventWriterT (withReflexWriterT f dw)

-- | Change the monad underlying an EventWriterT
mapEventWriterT
  :: (forall x. m x -> n x)
  -> EventWriterT t w m a
  -> EventWriterT t w n a
mapEventWriterT f (EventWriterT a) = EventWriterT $ mapReflexWriterT f a

-- TODO: Remove these implementations
instance Requester t m => Requester t (EventWriterT t w m) where
  type Request (EventWriterT t w m) = Request m
  type Response (EventWriterT t w m) = Response m
  requesting = lift . requesting
  requesting_ = lift . requesting_

instance (MonadQuery t q m, Monad m) => MonadQuery t q (EventWriterT t w m) where
  tellQueryIncremental = lift . tellQueryIncremental
  askQueryResult = lift askQueryResult
  queryIncremental = lift . queryIncremental

instance DynamicWriter t w m => DynamicWriter t w (EventWriterT t v m) where
  tellDyn = lift . tellDyn

instance PrimMonad m => PrimMonad (EventWriterT t w m) where
  type PrimState (EventWriterT t w m) = PrimState m
  primitive = lift . primitive

instance PerformEvent t m => PerformEvent t (EventWriterT t w m) where
  type Performable (EventWriterT t w m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent = lift . performEvent

instance TriggerEvent t m => TriggerEvent t (EventWriterT t w m) where
  newTriggerEvent = lift newTriggerEvent
  newTriggerEventWithOnComplete = lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete = lift . newEventWithLazyTriggerWithOnComplete
