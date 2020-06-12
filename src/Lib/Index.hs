-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib.Index where

import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving
import Search.SearchT
import Search.DFS
import Synth.Spec (Spec, SynthFn)
import Synth.Context
import Synth.LazyFeatures
import qualified Synth.Spec as Spec
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Synth.Ints2Int (synthInts2IntE)
import Data.Default (def)
import Util.Imports

data Index = Index { row :: Int, col :: Int } deriving (Eq, Ord)

derivingUnbox "Index"
    [t|  Index -> (Int, Int) |]
    [| \(Index i j) -> (i, j) |]
    [| \(i, j) -> Index i j |]

instance Show Index where
  show (Index i j) = "(" ++ show i ++ "," ++ show j ++ ")"

transpose :: Index -> Index
transpose (Index m n) = Index n m

scale :: Int -> Index -> Index
scale k (Index m n) = Index (k * m) (k * n)

--------------------
-- Instances
-------------------

instance Num Index where
  Index m1 n1 + Index m2 n2 = Index (m1+m2) (n1+n2)
  Index m1 n1 - Index m2 n2 = Index (m1-m2) (n1-n2)

instance (Monad m) => HasBasicLazyFeatures m Index Int where
  getBasicLazyFeatures idxs = LazyFeatures $ choice "Index.HasBasicFeatures.Int" [
    ("row",  pure $ Ex.map row idxs),
    ("col",  pure $ Ex.map col idxs),
    ("max",  pure $ Ex.map (\(Index r c) -> max r c) idxs),
    ("min",  pure $ Ex.map (\(Index r c) -> min r c) idxs),
    ("diff", pure $ Ex.map (\(Index r c) -> r - c) idxs)
    ]


instance Default Index where
  def = Index 0 0
