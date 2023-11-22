{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif

-- There are two expected orphan instances in this module:
--   * MonadSample (Pure t) ((->) t)
--   * MonadHold (Pure t) ((->) t)
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Module: Reflex.Pure
-- Description:
--   This module provides a pure implementation of Reflex, which is intended to
--   serve as a reference for the semantics of the Reflex class.  All
--   implementations of Reflex should produce the same results as this
--   implementation, although performance and laziness/strictness may differ.
module Reflex.Pure
  ( Pure
  , Behavior (..)
  , Event (..)
  , Dynamic (..)
  , Incremental (..)
  ) where

import Control.Monad
import qualified Data.Dependent.Map as DMap
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.MemoTrie
import Data.Type.Coercion
import Reflex.Class
import Data.Kind (Type)
import Control.Monad.Trans.Maybe
import qualified Data.List.NonEmpty as NonEmpty
import Data.Semigroup (sconcat)
import Control.Monad.Fix (MonadFix)

-- | A completely pure-functional 'Reflex' timeline, identifying moments in time
-- with the type @/t/@.
data Pure (t :: Type)

occurs :: Event (Pure t) a -> (t -> Maybe a)
occurs = unEvent

toEvent :: HasTrie t => (t -> Maybe a) -> Event (Pure t) a
toEvent = Event . memo

-- | The 'Enum' instance of @/t/@ must be dense: for all @/x :: t/@, there must not exist
-- any @/y :: t/@ such that @/'pred' x < y < x/@. The 'HasTrie' instance will be used
-- exclusively to memoize functions of @/t/@, not for any of its other capabilities.
instance (Enum t, HasTrie t, Ord t) => Reflex (Pure t) where
  newtype Behavior (Pure t) a = Behavior { unBehavior :: t -> a }
    deriving (Functor,Applicative,Monad,MonadFix)
  newtype Event (Pure t) a = Event { unEvent :: t -> Maybe a }
  type PushM (Pure t) = (->) t
  never = toEvent (pure Nothing)
  pushCheap f = toEvent . runMaybeT . (MaybeT . f <=< MaybeT . occurs)
  fanG e = EventSelectorG $ \k -> Event $ unEvent e >=> DMap.lookup k
  cacheEvent = id
  switchUncached :: Behavior (Pure t) (Event (Pure t) a) -> Event (Pure t) a
  switchUncached = toEvent . (occurs <=< sample)
  coincidenceUncached :: Event (Pure t) (Event (Pure t) a) -> Event (Pure t) a
  coincidenceUncached = push occurs
  behaviorCoercion Coercion = Coercion
  eventCoercion Coercion = Coercion
  fanInt e = EventSelectorInt $ \k -> Event $ unEvent e >=> IntMap.lookup k
  mergeListUncached es = Event $ \t ->
    fmap sconcat . NonEmpty.nonEmpty . mapMaybe (($ t) . unEvent) $ es
  
instance MonadSample (Pure t) ((->) t) where
  sample = unBehavior

instance (Enum t, HasTrie t, Ord t) => MonadHold (Pure t) ((->) t) where
  liftPush = id
  hold a e initialTime = hold' a
    where hold' initialValue = Behavior f
            where f = memo $ \sampleTime ->
                    -- Really, the sampleTime should never be prior to the initialTime,
                    -- because that would mean the Behavior is being sampled before
                    -- being created.
                    if sampleTime <= initialTime
                    then initialValue
                    else let lastTime = pred sampleTime
                             lastValue = f lastTime
                         in fromMaybe lastValue $ unEvent e lastTime
  now t = Event $ guard . (t ==)
