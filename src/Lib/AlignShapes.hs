-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.AlignShapes where

import Debug.Trace
import Lib.Blank
import Lib.Color
import Lib.Axis
import Util.Imports
import Lib.Grid (Grid)
import qualified Util.List as List
import qualified Util.Map as Map
import qualified Data.Maybe as Maybe
import qualified Lib.Index as Index
import Lib.Axis (Axis(..))
import qualified Lib.Axis as Axis
import Synth1.Basic
import Search.SearchT
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import qualified Data.List as List
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Data.Map as Map
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import qualified Data.UnionFind.ST as UnionFind
import Data.UnionFind.ST (Point)
import Lib.HasElems
import Control.Monad.ST
import Data.STRef

{-
It just occurred to me that this file doesn't make sense.
This is a patch to stop the bleeding.
-}

sanityCheckAlignment :: (HasBlank a, Eq a, Ord a) => [Shape a] -> [Maybe (Shape a)] -> Bool
sanityCheckAlignment inShapes labels = Maybe.isJust $ do
  guard $ length inShapes == length labels

  _ <- List.iterM inShapes Shape.empty $ \acc inShape -> do
    guard $ not (Shape.intersects acc inShape)
    pure $ Shape.union acc inShape

  _ <- List.iterM labels Shape.empty $ \acc label ->
    case label of
      Nothing -> pure acc
      Just outShape -> do
        guard $ not (Shape.intersects acc outShape)
        pure $ Shape.union acc outShape

  pure ()

data Shape2ShapeIntersectsUniqueKind = ColorsMustMatch | ColorsNeedNotMatch deriving (Eq, Ord, Show)

alignShape2ShapePred :: (HasBlank a, Eq a) => (Shape a -> Shape a -> Bool) -> [Shape a] -> [Shape a] -> Maybe [Maybe (Shape a)]
alignShape2ShapePred phi inShapes outShapes =
  flip mapM inShapes $ \inShape ->
    case filter (phi inShape) outShapes of
      [] -> pure $ Nothing
      [outShape] -> pure $ Just outShape
      _ -> Nothing

revAlignPoint2Shape :: (HasBlank a, Ord a) => Int -> [Shape a] -> [Shape a] -> Maybe [Maybe (Shape a)]
revAlignPoint2Shape acceptableDist inShapes outShapes = do
  in2out :: Map (Shape a) (Shape a) <- List.iterM outShapes Map.empty $ \acc outShape -> do
    case filter (Shape.intersects outShape) inShapes of
      [inShape] -> pure $ Map.insertWith Shape.union inShape outShape acc
      _         -> Map.iterM (Shape.idx2val outShape) acc $ \acc idx val -> do
        minDist :: Int <- do
          -- ortho dist? both?
          minDists <- mapM (Shape.minDistToIdx DiagDist idx) inShapes
          guard . not . null $ minDists
          pure $ minimum minDists
        guard $ minDist <= acceptableDist
        let closestIn = filter (\inShape -> Shape.minDistToIdx DiagDist idx inShape == Just minDist) inShapes
        guard $ length closestIn == 1
        pure $ Map.insertWith Shape.union (head closestIn) (Shape.singleton idx val) acc
  pure $ flip map inShapes $ \inShape ->
    case Map.lookup inShape in2out of
      Just outShape -> do
        guard . not . Shape.null $ outShape
        pure $ outShape
      Nothing -> Nothing

data Options = Shape2ShapeIntersectsUnique Shape2ShapeIntersectsUniqueKind | RevAlignPoint2Shape Int deriving (Eq, Ord, Show)

alignShapes :: (HasBlank a, Ord a) => Options -> [Shape a] -> [Shape a] -> Maybe [Maybe (Shape a)]
alignShapes opts inShapes outShapes = do
  labels <- core opts inShapes outShapes
  let ok = sanityCheckAlignment inShapes labels
  unless ok (traceM $ "WARNING: insane alignment, not using it")
  guard ok
  pure labels

  where
    core (Shape2ShapeIntersectsUnique ColorsMustMatch)    = alignShape2ShapePred (\s1 s2 -> Shape.intersects s1 s2 && Shape.subsetMatches s1 s2)
    core (Shape2ShapeIntersectsUnique ColorsNeedNotMatch) = alignShape2ShapePred (\s1 s2 -> Shape.intersects s1 s2)
    core (RevAlignPoint2Shape d)                          = revAlignPoint2Shape d
