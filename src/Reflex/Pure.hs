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
import Data.Dependent.Map (DMap)
import Data.GADT.Compare (GCompare)
import qualified Data.Dependent.Map as DMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.MemoTrie
import Data.Monoid
import Data.Type.Coercion
import Reflex.Class
import Data.Kind (Type)
import Control.Monad.Trans.Maybe
import qualified Data.List.NonEmpty as NonEmpty
import Data.Semigroup (sconcat)

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
  newtype Event (Pure t) a = Event { unEvent :: t -> Maybe a }

  type PushM (Pure t) = (->) t
  type PullM (Pure t) = (->) t

  never :: Event (Pure t) a
  never = toEvent (pure Nothing)

  pushCheap :: (a -> PushM (Pure t) (Maybe b)) -> Event (Pure t) a -> Event (Pure t) b
  pushCheap f = toEvent . runMaybeT . (MaybeT . f <=< MaybeT . occurs)

  pull :: PullM (Pure t) a -> Behavior (Pure t) a
  pull = Behavior . memo
--  The instance signature doeesn't compile, leave commented for documentation
--  fanG :: GCompare k => Event (Pure t) (DMap k v) -> EventSelectorG (Pure t) k v
  fanG e = EventSelectorG $ \k -> Event $ unEvent e >=> DMap.lookup k
  cacheEvent = id
  switchUncached :: Behavior (Pure t) (Event (Pure t) a) -> Event (Pure t) a
  switchUncached = toEvent . (occurs <=< sample)
  coincidenceUncached :: Event (Pure t) (Event (Pure t) a) -> Event (Pure t) a
  coincidenceUncached = push occurs
  unsafeBuildIncremental readV = Incremental (pull readV)
  behaviorCoercion Coercion = Coercion
  eventCoercion Coercion = Coercion
  -- dynamicCoercion Coercion = Coercion
  -- incrementalCoercion Coercion Coercion = Coercion
  fanInt e = EventSelectorInt $ \k -> Event $ unEvent e >=> IntMap.lookup k
  -- [UNUSED_CONSTRAINT]: The following type signature for merge will produce a
  -- warning because the GCompare instance is not used; however, removing the
  -- GCompare instance produces a different warning, due to that constraint
  -- being present in the original class definition.
  mergeListUncached es = Event $ \t ->
    fmap sconcat . NonEmpty.nonEmpty . mapMaybe (($ t) . unEvent) $ es
  
mergeIncrementalImpl :: (PatchTarget p ~ DMap k q, GCompare k)
  => (forall a. q a -> Event (Pure t) (v a))
  -> Incremental (Pure t) p -> Event (Pure t) (DMap k v)
mergeIncrementalImpl nt i = Event $ \t ->
  let results = DMap.mapMaybeWithKey (\_ q -> case nt q of Event e -> e t) $ unBehavior (currentIncremental i) t
  in if DMap.null results
     then Nothing
     else Just results

mergeIntIncrementalImpl :: (PatchTarget p ~ IntMap (Event (Pure t) a)) => Incremental (Pure t) p -> Event (Pure t) (IntMap a)
mergeIntIncrementalImpl i = Event $ \t ->
  let results = IntMap.mapMaybeWithKey (\_ (Event e) -> e t) $ unBehavior (currentIncremental i) t
  in if IntMap.null results
     then Nothing
     else Just results

instance MonadSample (Pure t) ((->) t) where

  sample :: Behavior (Pure t) a -> (t -> a)
  sample = unBehavior

instance (Enum t, HasTrie t, Ord t) => MonadHold (Pure t) ((->) t) where
  buildIncremental getInitialValue e initialTime =
    holdIncremental' (getInitialValue initialTime) e initialTime
  now t = Event $ guard . (t ==)

holdIncremental' :: (Ord t, Enum t, HasTrie t, Patch p) => PatchTarget p -> Event (Pure t) p -> t -> Incremental (Pure t) p
holdIncremental' initialValue e initialTime = Incremental (Behavior f) e
  where f = memo $ \sampleTime ->
          -- Really, the sampleTime should never be prior to the initialTime,
          -- because that would mean the Behavior is being sampled before
          -- being created.
          if sampleTime <= initialTime
          then initialValue
          else let lastTime = pred sampleTime
                   lastValue = f lastTime
               in case unEvent e lastTime of
                 Nothing -> lastValue
                 Just x -> fromMaybe lastValue $ apply x lastValue


  

