-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Direction where

import Lib.HasElems
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims
import Lib.Axis
import qualified Lib.Axis as Axis
import Lib.Index (Index(..))
import qualified Lib.Index as Index

import Synth1.Basic
import Search.SearchT

import qualified Util.List as List

data Direction = Normal | Reverse   deriving (Eq, Ord, Show)

reverse :: Direction -> Direction
reverse Normal  = Reverse
reverse Reverse = Normal

toScale :: Direction -> Int
toScale Normal = 1
toScale Reverse = -1

precedesAux :: Axis -> Index -> Index -> Bool
precedesAux Horizontal (Index row1 col1) (Index row2 col2) = col1 < col2
precedesAux Vertical (Index row1 col1) (Index row2 col2) = row1 < row2
precedesAux DownRight (Index row1 col1) (Index row2 col2) = row1 < row2
precedesAux DownLeft (Index row1 col1) (Index row2 col2) = row1 < row2

precedes :: Axis -> Direction -> Index -> Index -> Bool
precedes ax dir idx1 idx2 = case dir of
  Normal -> precedesAux ax idx1 idx2
  Reverse -> precedesAux ax idx2 idx1

idxsBetween :: Axis -> Index -> Index -> [Index]
idxsBetween ax idx1 idx2 = if precedes ax Normal idx1 idx2
  then idxsFromTo idx1 idx2 ax
  else idxsFromTo idx2 idx1 ax

step :: Index -> Int -> Axis -> Direction -> Index
step idx k ax dir =
  let dirScale = Lib.Direction.toScale dir
      (Index i j) = Axis.toDelta ax
      moveVector = Index (i * k) (j * k) in
    idx + (Index.scale dirScale moveVector)


furthestInAxDir :: [Index] -> Axis -> Direction -> Index
furthestInAxDir idxs ax dir =
  let scalar :: Int = if dir == Normal then 1 else -1
      maxFun :: Index -> Int = case ax of
        Horizontal -> \(Index i j) -> j
        Vertical -> \(Index i j) -> i
        DownRight -> \(Index i j) -> i + j
        DownLeft -> \(Index i j) -> i - j in
    List.argmaxKey (\idx -> scalar * (maxFun idx)) idxs


instance HasElems Direction where
  elems = [Normal, Reverse]

instance HasElems (Axis, Direction) where
  elems = [(ax, dir) | ax <- elems, dir <- elems]

instance (Monad m) => HasEnumVals m Direction where
  enumVals = oneOf "Direction.enumVals" [
    ("normal",  Normal),
    ("reverse", Reverse)
    ]

instance (Monad m) => HasEnumVals m [Direction] where
  enumVals = oneOf "DirectionSet.enumVals" [
    ("both",    [Normal, Reverse]),
    ("normal",  [Normal]),
    ("reverse", [Reverse])
    ]

instance (Monad m) => HasEnumVals m (Axis, Direction) where
  enumVals = do
    (ax :: Axis) <- enumVals
    (dir :: Direction) <- enumVals
    pure $ (ax, dir)

instance (Monad m) => HasEnumVals m [(Axis, Direction)] where
  enumVals = do
    (axs :: [Axis]) <- enumVals
    (dirs :: [Direction]) <- enumVals
    pure $ [(ax, dir) | ax <- axs, dir <- dirs]
