-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Ordering where

import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Map as Map

import Debug.Trace

import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import Lib.Axis (Axis(..))
import Lib.Blank
import Lib.Color
import Lib.Corner
import Lib.Grid (Grid)
import qualified Lib.Index as Index
import qualified Lib.Axis as Axis
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import Lib.HasElems

import Synth1.Basic
import Search.SearchT

import Util.Imports
import qualified Util.List as List
import qualified Util.Map as Map
import Util.List (range)




data Cycle = Snake | Zigzag deriving (Eq, Ord, Show)

instance (Monad m) => HasEnumVals m Cycle where
  enumVals = oneOf "Cycle.enumVals" [
    ("zigzag",  Zigzag),
    ("snake", Snake)
    ]

-- TODO (perf): In lean, this was slow due to cartesian product. An alternative we hadn't yet implemented
-- was just to iterate over the idxs and map to a new idx given the dir/corn/cyc. However, maybe
-- the cartesian product isn't as slow in haskell due to laziness?
getOrdering :: Axis -> Corner -> Cycle -> Dims -> Maybe [Index]
getOrdering ax corn cyc (Dims m n) = do
  -- better way to do this?
  guard $ Axis.isOrtho ax
  let rows :: [Int] = if isTop corn then range m else reverse (range m)
  let cols :: [Int] = if isLeft corn then range n else reverse (range n)
  -- [(row, col) | col <- range 2, row <- range 5]
  -- [(0,0),(1,0),(2,0),(3,0),(4,0),(0,1),(1,1),(2,1),(3,1),(4,1)]
  let idxs :: [Index] = case ax of
        Vertical -> [Index row col | col <- cols, row <- rows] -- rows gets enumerated first
        Horizontal -> [Index row col | row <- rows, col <- cols] --cols gets enumerated first
  if cyc == Zigzag then Just idxs
  else
    case ax of
      Horizontal -> Just (concat (flip List.mapWithIndex (List.split m idxs) (\idx rowIdxs -> if idx `mod` 2 == 0 then rowIdxs else reverse rowIdxs)))
      Vertical -> Just (concat (flip List.mapWithIndex (List.split n idxs) (\idx colIdxs -> if idx `mod` 2 == 0 then colIdxs else reverse colIdxs)))
