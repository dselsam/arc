-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Motion where

import Util.Imports
import Lib.HasElems
import Data.Maybe (maybeToList)
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims
import Lib.Axis (Axis(..))
import Lib.Direction (Direction(..))
import qualified Lib.Axis as Axis
import qualified Lib.Direction as Direction
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import Lib.Index (Index(..))
import qualified Lib.Index as Index
import Lib.Color
import Lib.Blank
import Lib.Shape (Shape(Shape))
import Synth1.Basic
import Data.Vector.Unboxed.Base (Unbox)
import Search.SearchT
import qualified Lib.Shape as Shape
import qualified Lib.Rect as Rect
import qualified Util.List as List
import qualified Util.Int as Int
import qualified Lib.Grid as Grid
import Lib.Grid (Grid)

------------------------------------------------------------------
-- This file contains the (simple, linear, low-level) motion DSL

-- We say "low-level" because:
--  - we do not handle moving *towards* something here.
------------------------------------------------------------------

data Trail = NoTrail | WithTrail Int deriving (Eq, Ord, Show)

data Motion =  Motion {
  axis  :: Axis,
  dir   :: Direction,
  steps :: Maybe Int,
  trail :: Trail
  } deriving (Eq, Ord, Show)

-- WARNING: assumes that steps >= 0
apply :: (Unbox a, HasBlank a) => Motion -> Grid a -> Shape a -> Shape a
apply motion@(Motion ax dir nSteps trail) g inShape = runIdentity $ do
  let delta = getDelta motion
  let newShape = applyCore delta 0 inShape
  pure newShape

  where
    applyCore delta i s =
      if Just i == nSteps
      then s
      else
        let candidate = Shape.move inShape ((i+1) * delta) ax dir in
          if shapeInvalidWrt g inShape candidate
          then s
          else
            let newShape = case trail of NoTrail -> candidate; WithTrail _ -> Shape.union s candidate in
              applyCore delta (i+1) newShape

    getDelta :: Motion -> Int
    getDelta (Motion _ _ _ (WithTrail delta)) = delta
    getDelta _ = 1

slideReaches :: (Unbox a, HasBlank a, Show a) => Grid a -> Shape a -> Shape a -> [(Axis, Direction)]
slideReaches g inShape outShape = do
  let inRect  = Shape.enclosingRect inShape
  let outRect = Shape.enclosingRect outShape
  ax  <- [Horizontal, Vertical, DownRight, DownLeft]
  guard $ Axis.onSame ax (Rect.upperLeft inRect) (Rect.upperLeft outRect)
  dir <- [Normal, Reverse]
  -- (We allow the null motion)
  guard . not $ Direction.precedes ax dir (Rect.upperLeft outRect) (Rect.upperLeft inRect)
  let motion = Motion ax dir Nothing NoTrail
  let movedShape = apply motion g inShape
  guard $ movedShape == outShape
  pure (ax, dir)

slideSteps :: (Unbox a, HasBlank a) => Grid a -> Shape a -> Shape a -> [(Axis, Direction, Int)]
slideSteps g inShape outShape = do
  -- TODO: guard that the normalized shapes are the same?
  -- We are awkwardly repeating work here and in the alignment
  let inRect  = Shape.enclosingRect inShape
  let outRect = Shape.enclosingRect outShape
  ax  <- [Horizontal, Vertical, DownRight, DownLeft]
  guard $ Axis.onSame ax (Rect.upperLeft inRect) (Rect.upperLeft outRect)
  dir <- [Normal, Reverse]
  -- (We allow the null motion)
  guard . not $ Direction.precedes ax dir (Rect.upperLeft outRect) (Rect.upperLeft inRect)
  let k = Axis.distAlongAxis ax (Rect.upperLeft inRect) (Rect.upperLeft outRect)
  let motion = Motion ax dir (Just k) NoTrail
  guard $ apply motion g inShape == outShape
  pure (ax, dir, k)

slideTrailReaches :: (Unbox a, HasBlank a) => Grid a -> Shape a -> Shape a -> [(Axis, Direction, Int)] -- the int is the delta
slideTrailReaches g inShape outShape = do
  guard $ Shape.subsetMatches inShape outShape
  ax    <- [Horizontal, Vertical, DownRight, DownLeft]
  dir   <- [Normal, Reverse]
  delta <- List.stableUniqKey id [1, Shape.minimalNonSelfIntersectingDelta inShape ax dir]
  let newShape = apply (Motion ax dir Nothing (WithTrail delta)) g inShape
  guard $ newShape == outShape
  -- TODO: extra guard motivated by not trying to use slideWithTrail for 4f537728?
  pure $ (ax, dir, delta)

nFree :: (Unbox a, HasBlank a) => Grid a -> Shape a -> Axis -> Direction -> Int
nFree g s0 ax dir = core 0 s0 where
  core i s =
    let candidate = Shape.move s0 (i+1) ax dir in
      if shapeInvalidWrt g s0 candidate
      then i
      else core (i+1) candidate

shapeInvalidWrt :: (Unbox a, HasBlank a) => Grid a -> Shape a -> Shape a -> Bool
shapeInvalidWrt g base candidate = flip any (Shape.indices candidate) $ \idx ->
  (not $ Dims.inBounds (Grid.dims g) idx)
  || (nonBlank (Grid.getD g idx) && (not $ Shape.containsIndex base idx))

alignShapes2ShapesD :: Grid Color -> [Shape Color] -> [Shape Color] -> [[Maybe (Shape Color)]]
alignShapes2ShapesD g inShapes outShapes = do
  -- TODO: filter that the alignment is injective
  let shape2shapes :: [[Maybe (Shape Color)]] = alignShape2Shapes g inShapes outShapes
  alignment <- fmap (take 20) $ List.cartesianProduct shape2shapes
  guard $ any Maybe.isJust alignment
  guard $ List.allDistinct (filter Maybe.isJust alignment)
  pure alignment

-- TODO: for now, "Nothing" means delete
alignShape2Shapes :: Grid Color -> [Shape Color] -> [Shape Color] -> [[Maybe (Shape Color)]]
alignShape2Shapes g inShapes outShapes =
  let outShapeSet = Set.fromList outShapes in
    flip map inShapes $ \inShape ->
      let allCandidates  = detectSubset outShapes inShape ++ detectNoTrail outShapeSet inShape
          uniqCandidates = List.stableUniqKey id allCandidates
      in
        if null uniqCandidates then [Nothing] else map Just uniqCandidates

  where
    detectNoTrail :: Set (Shape Color) -> Shape Color -> [Shape Color]
    detectNoTrail outShapeSet inShape = do
      ax  <- [Horizontal, Vertical, DownRight, DownLeft]
      dir <- [Normal, Reverse]
      -- Note: will be *many* duplicates, but we can prune
      outShape <- maybeToList $ findNoTrail 0 outShapeSet inShape ax dir
      pure outShape

      where
        findNoTrail :: Int -> Set (Shape Color) -> Shape Color -> Axis -> Direction -> Maybe (Shape Color)
        findNoTrail i outShapeSet inShape ax dir = do
          let candidate = Shape.move inShape i ax dir
          guard $ all (Dims.inBounds (Grid.dims g)) (Shape.indices candidate)
          if Set.member candidate outShapeSet
            then Just candidate
            else findNoTrail (i+1) outShapeSet inShape ax dir

    detectSubset :: [Shape Color] -> Shape Color -> [Shape Color]
    detectSubset outShapes inShape = do
      outShape <- outShapes
      guard $ inShape /= outShape
      guard $ Shape.subsetMatches inShape outShape
      pure outShape
