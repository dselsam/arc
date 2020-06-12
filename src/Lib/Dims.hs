-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StrictData #-}
module Lib.Dims where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Util.Imports
import Data.Hashable
import qualified Util.Int as Int
import Lib.Index
import Synth1.Basic
import Search.SearchT
import Search.DFS
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.Spec (Spec, SynthFn, SynthFn1)
import qualified Synth.Spec as Spec
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Synth.Ints2Int (synthInts2IntE)
import Util.List (range)
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving

data Dims = Dims { nRows :: Int, nCols :: Int } deriving (Eq, Ord, Show, Generic)

instance NFData Dims

derivingUnbox "Dims"
    [t|  Dims -> (Int, Int) |]
    [| \(Dims dx dy) -> (dx, dy) |]
    [| \(dx, dy) -> Dims dx dy |]

instance Hashable Dims where
  hashWithSalt salt dims = hashWithSalt salt (nRows dims, nCols dims)

iterM :: (Monad m) => Dims -> b -> (b -> Index -> m b) -> m b
iterM (Dims m n) init f =
  Int.iterM m init $ \acc i ->
    Int.iterM n acc $ \acc j -> f acc (Index i j)

iter :: Dims -> b -> (b -> Index -> Identity b) -> b
iter dims init f = runIdentity $ iterM dims init f

inBounds :: Dims -> Index -> Bool
inBounds (Dims m n) (Index r c) = r >= 0 && r < m && c >= 0 && c < n

allIdxs :: Dims -> [Index]
allIdxs (Dims m n) = [Index row col | col <- range n, row <- range m]

nIdxs :: Dims -> Int
nIdxs (Dims m n) = m * n

int2index :: Dims -> Int -> Index
int2index (Dims m n) i
  | n > 0 = Index (div i n) (mod i n)
  | otherwise = error "int2index div by 0"

index2int :: Dims -> Index -> Int
index2int ds@(Dims m n) idx@(Index row col)
  | inBounds ds idx = row * n + col
  | otherwise = error "index2int idx not in bounds"

firstM :: (Monad m) => Dims -> (Index -> m (Maybe a)) -> m (Maybe a)
firstM (Dims m n) f = Int.firstM m $ \i -> Int.firstM n $ \j -> f (Index i j)

first :: Dims -> (Index -> Identity (Maybe a)) -> Maybe a
first dims f = runIdentity $ firstM dims f

all :: Dims -> (Index -> Bool) -> Bool
all dims p = isNothing $ first dims $ \idx -> pure $ if not (p idx) then Just () else Nothing

allSame :: (Eq a) => Dims -> (Index -> a) -> Bool
allSame (Dims 0 0) key = True
allSame dims       key = Lib.Dims.all dims (\idx -> key idx == key (Index 0 0))

any :: Dims -> (Index -> Bool) -> Bool
any dims p = isJust $ first dims $ \idx -> pure $ if p idx then Just () else Nothing

transpose :: Dims -> Dims
transpose (Dims m n) = Dims n m

onTop     _          (Index x _) = x == 0
onLeft    _          (Index _ y) = y == 0
onBottom  (Dims m _) (Index x _) = x == m-1
onRight   (Dims _ n) (Index _ y) = y == n-1

edgePredicates :: Dims -> [Index -> Bool]
edgePredicates dims = map (\f -> f dims) $ [onTop, onLeft, onBottom, onRight]

onEdge  :: Dims -> Index -> Bool
onEdge dims idx = Prelude.any (\p -> p idx) $ edgePredicates dims

nEdgesOn :: Dims -> Index -> Int
nEdgesOn dims idx = length . filter (\p -> p idx) $ edgePredicates dims

---------------------
-- Features
---------------------

isSquare (Dims m n) = m == n
isSkinny (Dims m n) = m > n
isFat    (Dims m n) = n > m
nCells   (Dims m n) = m * n


instance (Monad m) => HasEnumBoolFeatures m Dims where
  enumBoolFeatures = choice "Dims.enumBoolFeatures" [
    ("isSquare",          pure isSquare),
    ("isSkinny",          pure isSkinny),
    ("isFat",             pure isFat)
    ]

instance (Monad m) => HasEnumIntFeatures m Dims where
  enumIntFeatures = choice "Dims.enumIntFeatures" [
    ("nRows",          pure nRows),
    ("nCols",          pure nCols),
    ("nCells",         pure nCells)
    ]

--------------------
-- Instances
-------------------

instance Num Dims where
  Dims m1 n1 + Dims m2 n2 = Dims (m1+m2) (n1+n2)
  Dims m1 n1 - Dims m2 n2 = Dims (m1-m2) (n1-n2)
  Dims m1 n1 * Dims m2 n2 = Dims (m1*m2) (n1*n2)

instance (Monad m) => HasBasicLazyFeatures m Dims Bool where
  getBasicLazyFeatures dimss = LazyFeatures $ choice "Dims.getBasicLazyFeatures.Bools" [
    ("isSquare", pure $ Ex.map isSquare dimss),
    ("isSkinny", pure $ Ex.map isSkinny dimss)
    ]

instance (Monad m) => HasBasicLazyFeatures m Dims Int where
  getBasicLazyFeatures dimss = LazyFeatures $ choice "Dims.getBasicLazyFeatures.Int" [
    ("nRows",   pure $ Ex.map nRows dimss),
    ("nCols",   pure $ Ex.map nCols dimss),
    -- TODO: worth including these? we often want m - 1 - <k>
    ("nRows-1", pure $ Ex.map (\d -> nRows d - 1) dimss),
    ("nCols-1", pure $ Ex.map (\d -> nCols d - 1) dimss)
    ]
