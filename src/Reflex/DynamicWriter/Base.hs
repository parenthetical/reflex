{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif


{-# LANGUAGE PartialTypeSignatures #-} -- TODO: remove


module Reflex.DynamicWriter.Base
  ( DynamicWriterT (..)
  , runDynamicWriterT
  , withDynamicWriterT
  , mapDynamicWriterT
  ) where

import Control.Monad.Exception
import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Morph
import Control.Monad.Primitive
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.State.Strict

import Reflex.Adjustable.Class
import Reflex.Class
import Reflex.DynamicWriter.Class
import Reflex.EventWriter.Class (EventWriter, tellEvent)
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

-- | A basic implementation of 'DynamicWriter'.
newtype DynamicWriterT t w m a = DynamicWriterT { unDynamicWriterT :: ReflexWriterT w Dynamic t m a }
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

-- | Run a 'DynamicWriterT' action.  The dynamic writer output will be provided
-- along with the result of the action.
runDynamicWriterT :: (MonadFix m, Reflex t, Monoid w) => DynamicWriterT t w m a -> m (a, Dynamic t w)
runDynamicWriterT = runReflexWriterT . unDynamicWriterT

instance (Adjustable t m, Monoid w, MonadHold t m, MonadFix m) => Adjustable t (DynamicWriterT t w m) where
  runWithReplace v0 = DynamicWriterT . runWithReplace (coerce v0) . fmap coerce
  traverseIntMapWithKeyWithAdjust f m e = DynamicWriterT $ traverseIntMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjust f m e = DynamicWriterT $ traverseDMapWithKeyWithAdjust (\k v -> coerce (f k v)) m (fmap coerce e)
  traverseDMapWithKeyWithAdjustWithMove f m e = DynamicWriterT $ traverseDMapWithKeyWithAdjustWithMove (\k v -> coerce (f k v)) m (fmap coerce e)


instance (Monad m, Monoid w, Reflex t) => DynamicWriter t w (DynamicWriterT t w m) where
  tellDyn w = DynamicWriterT $ tell w

-- TODO: Implement this using MonadTransControl.
-- | Map a function over the output of a 'DynamicWriterT'.
withDynamicWriterT :: (Monoid w, Monoid w', Reflex t, MonadHold t m)
                   => (w -> w')
                   -> DynamicWriterT t w m a
                   -> DynamicWriterT t w' m a
withDynamicWriterT f (DynamicWriterT dw) = DynamicWriterT (withReflexWriterT f dw)

-- | Change the monad underlying an DynamicWriterT
mapDynamicWriterT
  :: (forall x. m x -> n x)
  -> DynamicWriterT t w m a
  -> DynamicWriterT t w n a
mapDynamicWriterT f (DynamicWriterT a) = DynamicWriterT $ mapReflexWriterT f a

-- TODO: Remove these implementations
instance Requester t m => Requester t (DynamicWriterT t w m) where
  type Request (DynamicWriterT t w m) = Request m
  type Response (DynamicWriterT t w m) = Response m
  requesting = lift . requesting
  requesting_ = lift . requesting_

instance (MonadQuery t q m, Monad m) => MonadQuery t q (DynamicWriterT t w m) where
  tellQueryIncremental = lift . tellQueryIncremental
  askQueryResult = lift askQueryResult
  queryIncremental = lift . queryIncremental

instance EventWriter t w m => EventWriter t w (DynamicWriterT t v m) where
  tellEvent = lift . tellEvent

instance PerformEvent t m => PerformEvent t (DynamicWriterT t w m) where
  type Performable (DynamicWriterT t w m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent = lift . performEvent

instance TriggerEvent t m => TriggerEvent t (DynamicWriterT t w m) where
  newTriggerEvent = lift newTriggerEvent
  newTriggerEventWithOnComplete = lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete = lift . newEventWithLazyTriggerWithOnComplete

instance MonadState s m => MonadState s (DynamicWriterT t w m) where
  get = lift get
  put = lift . put

instance PrimMonad m => PrimMonad (DynamicWriterT t w m) where
  type PrimState (DynamicWriterT t w m) = PrimState m
  primitive = lift . primitive
