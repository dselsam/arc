-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Lib.Axis where

import Lib.HasElems
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims

import Lib.Index (Index(..))
import qualified Lib.Index as Index

import Synth1.Basic
import Search.SearchT
import Util.List (range)

data Axis = Horizontal | Vertical | DownLeft | DownRight deriving (Eq, Ord, Show)

isOrtho :: Axis -> Bool
isOrtho Horizontal = True
isOrtho Vertical   = True
isOrtho DownRight  = False
isOrtho DownLeft   = False

isDiag :: Axis -> Bool
isDiag = not . isOrtho

toDelta :: Axis -> Index
toDelta Horizontal = Index 0 1
toDelta Vertical   = Index 1 0
toDelta DownRight  = Index 1 1
toDelta DownLeft   = Index 1 (-1)

data DistType = OrthoDist | DiagDist deriving (Eq, Ord, Show)

dist :: DistType -> Index -> Index -> Int
dist OrthoDist (Index row1 col1) (Index row2 col2) = (abs (row1 - row2)) + (abs (col1 - col2))
dist DiagDist  (Index row1 col1) (Index row2 col2) = max (abs (row1 - row2)) (abs (col1 - col2))

distAlongAxis :: Axis -> Index -> Index -> Int
distAlongAxis Horizontal = dist OrthoDist
distAlongAxis Vertical   = dist OrthoDist
distAlongAxis DownRight  = dist DiagDist
distAlongAxis DownLeft   = dist DiagDist

-- TODO: put these in symmetry?
reflectAround :: Dims -> Axis -> Index -> Index

reflectAround (Dims m n) Horizontal (Index i j) = Index (m - 1 - i) j
reflectAround (Dims m n) Vertical   (Index i j) = Index i (n - 1 - j)

-- FIXME: This should throw a runtime error
reflectAround (Dims m n) DownRight  idx@(Index i j)
  | m == n    = Index j i
  | otherwise = idx -- TODO: optional features instead?

-- FIXME: This should throw a runtime error
reflectAround dims@(Dims m n) DownLeft idx
  | m == n    = rflt Vertical . rflt DownRight . rflt Vertical $ idx
  | otherwise = idx -- TODO: optional features instead?
  where
    rflt = reflectAround dims

onSame :: Axis -> Index -> Index -> Bool
onSame Horizontal idx1 idx2 = (Index.row idx1) == (Index.row idx2)
onSame Vertical idx1 idx2 = (Index.col idx1) == (Index.col idx2)
onSame DownRight idx1 idx2 = abs (Index.row idx1 - Index.row idx2) == abs (Index.col idx1 - Index.col idx2) && ((Index.row idx1 - Index.row idx2) * (Index.col idx1 - Index.col idx2)) > 0
onSame DownLeft idx1 idx2 = abs (Index.row idx1 - Index.row idx2) == abs (Index.col idx1 - Index.col idx2) && ((Index.row idx1 - Index.row idx2) * (Index.col idx1 - Index.col idx2)) < 0


idxsFromTo :: Index -> Index -> Axis -> [Index]
idxsFromTo idx1 idx2 Horizontal = flip map (range (abs (Index.col idx2 - Index.col idx1 - 1))) $ \diff ->
  idx1 + (Index 0 (1 + diff))
idxsFromTo idx1 idx2 Vertical = flip map (range (abs (Index.row idx2 - Index.row idx1 - 1))) $ \diff ->
  idx1 + (Index (1 + diff) 0)
idxsFromTo idx1 idx2 DownRight = flip map (range (abs (Index.row idx2 - Index.row idx1 - 1))) $ \diff ->
  idx1 + (Index (1 + diff) (1 + diff))
idxsFromTo idx1 idx2 DownLeft = flip map (range (abs (Index.row idx2 - Index.row idx1 - 1))) $ \diff ->
  idx1 - (Index (-1 * (1 + diff)) (1 + diff))


instance HasElems Axis where
  elems = [Horizontal, Vertical, DownRight, DownLeft]

instance (Monad m) => HasEnumVals m Axis where
  enumVals = oneOf "Axis.enumVals" [
    ("horizontal", Horizontal),
    ("vertical",   Vertical),
    ("downRight",  DownRight),
    ("downLeft",   DownLeft)
    ]

instance (Monad m) => HasEnumVals m [Axis] where
  enumVals = choice "Axis.enumVals" [
    ("all",      pure $ [Horizontal, Vertical, DownRight, DownLeft])
    , ("ortho",  pure $ [Horizontal, Vertical])
    , ("diag",   pure $ [DownRight, DownLeft])
    , ("single", do
          ax <- enumVals
          pure $ [ax]
      )
    ]
