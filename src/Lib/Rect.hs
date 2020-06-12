-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Lib.Rect where

import Debug.Trace
import Util.Imports
--import Lib.Grid (Grid)
import qualified Lib.Index as Index
import Synth1.Basic
import Search.SearchT
import Search.DFS
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import qualified Data.List as List
import qualified Lib.Dims as Dims
--import qualified Lib.Grid as Grid
import qualified Data.Map as Map
import Lib.Axis (Axis(..))
import qualified Lib.Axis as Axis
import Lib.Direction (Direction(..))
import qualified Lib.Direction as Direction
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.Spec (Spec, SynthFn, SynthFn1)
import qualified Synth.Spec as Spec
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Synth.Ints2Int (synthInts2IntE)
import Lib.Corner
import Lib.HasElems

data Rect = Rect {
  upperLeft :: Index,
  dims      :: Dims
  } deriving (Eq, Ord, Show)

-- Makers

empty :: Rect
empty = Rect (Index 0 0) (Dims 0 0)

singleton :: Index -> Rect
singleton idx = Rect { upperLeft = idx, dims = Dims 1 1 }

-- Helpers

containsIndex :: Rect -> Index -> Bool
containsIndex (Rect (Index m1 n1) (Dims dx dy)) (Index i j) =
  m1 <= i && i < (m1 + dx) && n1 <= j && j < (n1 + dy)

-- Transformations

move :: Rect -> Int -> Axis -> Direction -> Rect
move r k ax dir = r { upperLeft = upperLeft r + (Index.scale (k * Direction.toScale dir) (Axis.toDelta ax)) }

stripPerimeter :: Rect -> Rect
stripPerimeter (Rect ul dims) = Rect { upperLeft = ul + Index 1 1, dims = dims - Dims 2 2 }

addFrame :: Rect -> Rect
addFrame (Rect ul dims) = Rect (ul - Index 1 1) (dims + Dims 2 2)

shiftIndex :: Rect -> Index -> Rect
shiftIndex (Rect ul dims) idx = Rect (ul + idx) dims

shiftIndexRev :: Rect -> Index -> Rect
shiftIndexRev (Rect ul dims) idx = Rect (ul - idx) dims

fromDims :: Dims -> Rect
fromDims dims = Rect (Index 0 0) dims

intersect :: Rect -> Rect -> Rect
intersect r1 r2 =
  let rMin = max (minRow r1) (minRow r2)
      rMax = min (maxRow r1) (maxRow r2)
      cMin = max (minCol r1) (minCol r2)
      cMax = min (maxCol r1) (maxCol r2) in
    Rect (Index rMin cMin) (Dims (rMax + 1 - rMin) (cMax + 1 - cMin))

union :: Rect -> Rect -> Rect
union r1 r2 =
  let rMin = min (minRow r1) (minRow r2)
      rMax = max (maxRow r1) (maxRow r2)
      cMin = min (minCol r1) (minCol r2)
      cMax = max (maxCol r1) (maxCol r2) in
    Rect (Index rMin cMin) (Dims (rMax + 1 - rMin) (cMax + 1 - cMin))

-- TODO: dims to list and then map/filter?
getPerimeterIdxs :: Rect -> [Index]
getPerimeterIdxs (Rect ul dims@(Dims dx dy)) = Dims.iter dims [] $ \acc idx@(Index i j) -> pure $
  if (i == 0) || (j == 0) || (i + 1 == dx) || (j + 1 == dy)
  then (ul + idx):acc
  else acc

getIdxs :: Rect -> [Index]
getIdxs (Rect ul dims@(Dims dx dy)) = Dims.iter dims [] $ \acc idx@(Index i j) -> pure $ (ul + idx):acc

getInteriorIdxs :: Rect -> [Index]
getInteriorIdxs r = (getIdxs r) List.\\ (getPerimeterIdxs r)


-- Bool features

isSquare :: Rect -> Bool
isSquare = Dims.isSquare . dims

isLine :: Rect -> Bool
isLine (Rect _ (Dims dx dy)) = dx == 1 || dy == 1

-- TODO: more and put elsewhere
instance (Monad m) => HasEnumBoolFeatures m Rect where
  enumBoolFeatures = choice "Rect.enumBoolFeatures" [
    ("isSquare",      pure isSquare),
    ("isLine",        pure isLine)
    ]

-- Int features

nRows :: Rect -> Int
nRows (Rect _ (Dims dx _)) = dx

nCols :: Rect -> Int
nCols (Rect _ (Dims _ dy)) = dy

area :: Rect -> Int
area (Rect _ (Dims dx dy)) = dx * dy

perimeterSize :: Rect -> Int
perimeterSize (Rect _ (Dims dx dy)) = 2 * dx + 2 * dy

minRow :: Rect -> Int
minRow (Rect (Index x _) _) = x

minCol :: Rect -> Int
minCol (Rect (Index _ y) _) = y

maxRow :: Rect -> Int
maxRow (Rect (Index x _) (Dims dx _)) = x + dx - 1

maxCol :: Rect -> Int
maxCol (Rect (Index _ y) (Dims _ dy)) = y + dy - 1

-- r1 contains r2
contains2nd :: Rect -> Rect -> Bool
contains2nd r1 r2 =
  minRow r2 >= minRow r1
  && maxRow r2 <= maxRow r1
  && minCol r2 >= minCol r1
  && maxCol r2 <= maxCol r1

-- TODO: more and put elsewhere
instance (Monad m) => HasEnumIntFeatures m Rect where
  enumIntFeatures = choice "Rect.enumIntFeatures" [
    ("nRows",         pure Lib.Rect.nRows),
    ("nCols",         pure Lib.Rect.nCols),
    ("area",          pure area),
    ("perimeterSize", pure perimeterSize),
    ("minRow",        pure minRow),
    ("minCol",        pure minCol),
    ("maxRow",        pure maxRow),
    ("maxCol",        pure maxCol)
    ]

getCorner :: Rect -> Corner -> Index
getCorner (Rect ul rDims) TopLeft = ul
getCorner r TopRight = Index (minRow r) (maxCol r)
getCorner r BottomLeft = Index (maxRow r) (minCol r)
getCorner r BottomRight = Index (maxRow r) (maxCol r)

getCorners :: Rect -> [Index]
getCorners r@(Rect ul rDims) = flip map elems $ \corn -> getCorner r corn

getNonEdgeCorners :: Dims -> Rect -> [Index]
getNonEdgeCorners ds r@(Rect ul rDims) = filter (\idx -> not (Dims.onEdge ds idx)) $ getCorners r

-- TODO: split hasCenter and getCenter? or even hasCenterAlong Ax?
hasCenter :: Rect -> Bool
hasCenter (Rect ul (Dims dx dy)) =
  mod dx 2 == 1 && mod dy 2 == 1

getCenter :: Rect -> Maybe Index
getCenter (Rect ul (Dims dx dy)) = do
  guard $ mod dx 2 == 1 && mod dy 2 == 1
  pure $ ul + Index (div dx 2) (div dy 2)

flipIdxAroundCenter :: Rect -> Axis -> Index -> Index
flipIdxAroundCenter r Horizontal (Index x y) = Index (maxRow r - (x - minRow r)) y
flipIdxAroundCenter r Vertical   (Index x y) = Index x (maxCol r - (y - minCol r))

reflectIdxAroundSide :: Rect -> Axis -> Direction -> Index -> Index
reflectIdxAroundSide r@(Rect _ (Dims dx dy)) Horizontal Normal  (Index x y) = Index ((maxRow r + 2 * dx - 1) - (x - minRow r)) y
reflectIdxAroundSide r@(Rect _ (Dims dx dy)) Horizontal Reverse (Index x y) = Index ((minRow r - 1) - (x - minRow r)) y
reflectIdxAroundSide r@(Rect _ (Dims dx dy)) Vertical   Normal  (Index x y) = Index x ((minCol r + 2 * dy - 1) - (y - minCol r))
reflectIdxAroundSide r@(Rect _ (Dims dx dy)) Vertical   Reverse (Index x y) = Index x ((minCol r - 1) - (y - minCol r))

rmSide :: Rect -> Axis -> Direction -> Rect
rmSide (Rect (Index i j) (Dims dx dy)) ax dir =
  case (ax, dir) of
    (Vertical, Reverse)   -> Rect (Index (i+1) j)     (Dims (dx-1) dy)
    (Vertical, Normal)    -> Rect (Index i     j)     (Dims (dx-1) dy)
    (Horizontal, Reverse) -> Rect (Index i     (j+1)) (Dims dx     (dy-1))
    (Horizontal, Normal)  -> Rect (Index i     j)     (Dims dx     (dy-1))

-------------------------------------------
-- Instances
-------------------------------------------

instance (Monad m) => HasBasicLazyFeatures m Rect Int where
  getBasicLazyFeatures rs = LazyFeatures $ choice "Rect.HasBasicLazyFeatures.Int" [
      ("dims",          LazyFeatures.choose $ getBasicLazyFeatures (Ex.map dims rs)),
      ("minRow",        pure $ Ex.map minRow rs),
      ("minCol",        pure $ Ex.map minCol rs),
      ("maxRow",        pure $ Ex.map maxRow rs),
      ("maxCol",        pure $ Ex.map maxCol rs),
      ("area",          pure $ Ex.map area rs),
      ("perimeterSize", pure $ Ex.map perimeterSize rs)
      ]

instance (Monad m) => HasBasicLazyFeatures m Rect Bool where
  getBasicLazyFeatures rs = LazyFeatures $ choice "Rect.HasBasicLazyFeatures.Bool" [
      ("isLine",        pure $ Ex.map isLine rs),
      ("isSquare",      pure $ Ex.map isSquare rs)
      ]

instance Num Rect where
  Rect i1 d1 + Rect i2 d2 = Rect (i1+i2) (d1+d2)
  Rect i1 d1 - Rect i2 d2 = Rect (i1-i2) (d1-d2)
