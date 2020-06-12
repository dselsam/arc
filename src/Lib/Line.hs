-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Lib.Line where

import Lib.Axis
import Lib.Blank
import Lib.Direction (Direction(..))
import qualified Lib.Direction as Direction
import Lib.Index

import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims

import Util.List (range)
import qualified Util.Int as Int

-- for diag axes, the offset can be interpreted as the col
data Line = Line { ax :: Axis, offset :: Int } deriving (Eq, Ord, Show)

numAxLines :: Dims -> Axis -> Int
numAxLines (Dims m n) Horizontal = m
numAxLines (Dims m n) Vertical = n
numAxLines (Dims m n) DownRight = m + n - 1
numAxLines (Dims m n) DownLeft = m + n - 1

startRow :: Dims -> Axis -> Int -> Int
startRow (Dims m n) Horizontal id = id
startRow (Dims m n) Vertical id = 0
startRow (Dims m n) DownRight id = max 0 (id - (n - 1))
startRow (Dims m n) DownLeft id = max 0 (id - (n - 1))

startCol :: Dims -> Axis -> Int -> Int
startCol (Dims m n) Horizontal id = 0
startCol (Dims m n) Vertical id = id
startCol (Dims m n) DownRight id = max 0 (n - 1 - id)
startCol (Dims m n) DownLeft id = min id (n - 1)

startIdx :: Dims -> Axis -> Int -> Index
startIdx dims ax id = Index (startRow dims ax id) (startCol dims ax id)

idxAxisId :: Dims -> Axis -> Index -> Int
idxAxisId dims Horizontal (Index row col) = row
idxAxisId dims Vertical (Index row col) = col
idxAxisId (Dims m n) DownRight (Index row col) = row + (n - 1 - col)
idxAxisId dims DownLeft (Index row col) = row + col

firstRow :: Dims -> Line -> Int
firstRow (Dims m n) (Line Horizontal offset) = offset
firstRow (Dims m n) (Line Vertical offset) = 0
firstRow (Dims m n) (Line DownRight offset) = if offset < 0 then abs offset else 0
firstRow (Dims m n) (Line DownLeft offset) = if offset > (n - 1) then (abs offset) - (n - 1) else 0

firstCol :: Dims -> Line -> Int
firstCol (Dims m n) (Line Horizontal offset) = 0
firstCol (Dims m n) (Line Vertical offset) = offset
firstCol (Dims m n) (Line DownRight offset) = if offset < 0 then 0 else abs offset
firstCol (Dims m n) (Line DownLeft offset) = if offset > (n - 1) then n - 1 else abs offset

lastRow :: Dims -> Line -> Int
lastRow (Dims m n) (Line Horizontal offset) = offset
lastRow (Dims m n) (Line Vertical offset) = (m - 1)
lastRow (Dims m n) (Line DownRight offset) =
  if offset < 0 then min (n - 1 + (abs offset)) (m - 1)
  else min (n - 1 - (abs offset)) (m - 1)
lastRow (Dims m n) (Line DownLeft offset) = min (m - 1) (abs offset)

-- TODO: lineWith -> lineThrough
-- TODO: Axis before Index
lineWith :: Dims -> Index -> Axis -> Line
lineWith (Dims m n) (Index row col) Horizontal = Line Horizontal row
lineWith (Dims m n) (Index row col) Vertical = Line Vertical col
lineWith (Dims m n) (Index row col) DownRight = Line DownRight (col - row)
lineWith (Dims m n) (Index row col) DownLeft = Line DownLeft (col + row)

-- TODO: unnecessary -- doing duplicate work. really just need to compute the OFFSET for
-- a given identifier. Dont need to compute the startIdx
lineFromId :: Dims -> Axis -> Int -> Line
lineFromId dims ax id =
  let startIdx = Lib.Line.startIdx dims ax id in
    Lib.Line.lineWith dims startIdx ax

contains :: Line -> Index -> Bool
contains (Line Horizontal offset) (Index row col) = row == offset
contains (Line Vertical offset) (Index row col) = col == offset
contains (Line DownRight offset) (Index row col) = row == (offset - col)
contains (Line DownLeft offset) (Index row col) = row == (col - offset)

-- TODO: nElems -> nIdxs
nElems :: Dims -> Line -> Int
nElems (Dims m n) (Line Horizontal offset) = n
nElems (Dims m n) (Line Vertical offset) = m
nElems dims l@(Line DownRight offset) = (Lib.Line.lastRow dims l) + 1 - (Lib.Line.firstRow dims l)
nElems dims l@(Line DownLeft offset) = (Lib.Line.lastRow dims l) + 1 - (Lib.Line.firstRow dims l)


get :: Dims -> Line -> Int -> Index
get (Dims m n) (Line Horizontal offset) i = Index offset i
get (Dims m n) (Line Vertical offset) i = Index i offset
get dims l@(Line DownRight offset) i =
  let firstIdx = Index (Lib.Line.firstRow dims l) (Lib.Line.firstCol dims l) in
    Direction.step firstIdx i DownRight Normal
get dims l@(Line DownLeft offset) i =
  let firstIdx = Index (Lib.Line.firstRow dims l) (Lib.Line.firstCol dims l) in
    Direction.step firstIdx i DownLeft Normal

-- TODO: Build a shape unit? Check what this gets us
idxsOnLine :: Dims -> Line -> [Index]
idxsOnLine dims l = flip map (range (nElems dims l)) $ \i -> Lib.Line.get dims l i

-- TODO: Bad name. Maybe don't need
idxsOfId :: Dims -> Axis -> Int -> [Index]
idxsOfId dims ax id =
  let idLine = lineFromId dims ax id in
    idxsOnLine dims idLine
