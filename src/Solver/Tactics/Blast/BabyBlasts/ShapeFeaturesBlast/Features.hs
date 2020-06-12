{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.Features (synthShapeFeatureBlastMasks, synthShapeFeatureBlastCandidates) where

import Util.Imports
import qualified Util.List as List
import Util.List (uncurry4)
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Data.Foldable
import Data.Ratio

import Solver.SolveM
import Solver.Synth1Context
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Search.SearchT
import Search.Guess
import qualified Search.Entry as Entry
import qualified Search.History as History

import Lib.Axis (Axis(..))
import Lib.Direction (Direction(..))
import qualified Lib.Axis as Axis
import Synth1.Synth1Context
import Solver.Goal (Goal(..), StdGoal)
import qualified Solver.Goal as Goal
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import Lib.Shape (Shape)
import Lib.Rect (Rect)
import qualified Lib.Shape as Shape
import qualified Lib.Rect as Rect
import qualified Lib.Axis as Axis
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.HasElems
import qualified Util.List as List
import qualified Data.Vector.Unboxed as Vector

import Solver.Tactics.Blast.GlobalFeatures


synthShapeFeatureBlastMasks :: StdGoal -> Synth1M (Ex (Grid Bool))
synthShapeFeatureBlastMasks goal@(Goal inputs outputs ctx) = do
  (masks :: Ex (Grid Bool)) <- choice "ShapeFeatureBlast.synthMasks" [
    ("all", allMask goal)
    , ("blank", blankMask goal)
    , ("colorDepend", do
        cs <- choice "ShapeFeatureBlast.color" [
          ("standard", do
              cs <- Grid.enumRelevantColors inputs outputs
              pure cs),
          ("shapeDepend", do
              cs <- oneOf "ctx.colors" (ctxColors ctx)
              pure cs)
          ]
        choice "colorDepend" [
          ("isVal", isValMask goal cs)
          ])
    , ("isIdx", isIdxMask goal)
    , ("flankedBySpecialOnAx", flankedBySpecialOnAx goal)
    , ("idxInAnyAx", idxInAnyAxMask goal)
    , ("idxListInAnyAx", anyIdxInAnyAxMask goal)
    , ("idxInAxDir",
          -- TODO: Extend to handle axdirs
          idxInAxDirMask goal)
    , ("surroundedBySpecialOnAxes", surroundedBySpecialOnAxesMask goal)
    , ("containedInShape", containedInShapeMask goal)
    , ("containedInAnyShape", containedInAnyShapeMask goal)
    , ("containedInShapeEnclosingRect", containedInShapeEnclosingRectMask goal)
    , ("containedInAnyShapeEnclosingRect", containedInAnyShapeEnclosingRectMask goal)
    , ("containedInIdxListMask", containedInIdxListMask goal)
    , ("touchingAnyShapeOrtho", touchingAnyShapeOrthoMask goal)
    , ("touchingAnyShapeDiag", touchingAnyShapeDiagMask goal)
    , ("touchingAnyShapeAll", touchingAnyShapeAllMask goal)
    , ("touchingShapeOrtho", touchingShapeOrthoMask goal)
    , ("touchingShapeDiag", touchingShapeDiagMask goal)
    , ("touchingShapeAll", touchingShapeAllMask goal)
    , ("indirect", do
        intGrids :: Ex (Grid Int) <- choice "AxesBlast.index2int" [
          ("minDistToShape", minDistToShapeMask goal)
          , ("minDistToAnyShape", minDistToAnyShapeMask goal)
          ]
        boolGrids :: (Ex (Grid Bool)) <- choice "AxesBlast.int2boolMethod" [
          ("int2boolFn", do
              int2ints :: Ex (Int -> Int) <- enumInt2Int (ctxInts ctx)
              int2bools :: Ex (Int -> Bool) <- enumInt2Bool (ctxInts ctx)
              pure $ flip Ex.map (Ex.zip3 intGrids int2ints int2bools) $ \(intGrid, int2int, int2bool) -> do
                Grid.fromFunc (Grid.dims intGrid) $ \idx ->
                  int2bool (int2int (Grid.get intGrid idx))),
          ("int2boolExtreme", do
              (extremeVals :: Ex Int) <- choice "extreme" [
                ("maximum", pure $ flip Ex.map intGrids (\intG -> Vector.maximum (Grid.gridData intG))),
                ("minimum", pure $ flip Ex.map intGrids (\intG -> Vector.minimum (Grid.gridData intG)))
                ]
              pure $ flip Ex.map (Ex.zip intGrids extremeVals) (\(intG, xVal) ->
                  flip Grid.map intG (\idx val -> if val == xVal then True else False)))
          ]
        pure $ boolGrids)
    ]
  phi <- oneOf "negate" [("no",  id), ("yes", not)]
  pure $ flip Ex.map masks $ \mask -> flip Grid.map mask $ \_ b -> phi b



synthShapeFeatureBlastCandidates :: StdGoal -> Synth1M (Ex (Grid Color))
synthShapeFeatureBlastCandidates goal@(Goal inputs outputs ctx) =
  choice "synthCandidates" [
    ("blank", blankCandidate goal)
    , ("keep", pure inputs)
    , ("constCand", do
          cs <- choice "ShapeFeatureBlast.color" [
            ("standard", do
                cs <- Grid.enumRelevantColors inputs outputs
                pure cs),
            ("shapeDepend", do
                cs <- oneOf "ctx.colors" (ctxColors ctx)
                pure cs)
            ]
          constCandidate goal cs)
  ]





enumInt :: (Monad m, HasTrainTest m) => [Choice (Ex Int)] -> [Int] -> SearchT m (Ex Int)
enumInt ints consts =
  choice "enumInt" [
    ("const", do
      x <- oneOf "Int.enumConst" $ flip Prelude.map consts $ \k -> (show k, k)
      Ex.map (\_ -> x) <$> getDummyEx)
    , ("ctx", oneOf "ctx" ints)
  ]

-- want mod and div here because we are considering distance!
enumInt2Int :: (Monad m, HasTrainTest m) => [Choice (Ex Int)] -> SearchT m (Ex (Int -> Int))
enumInt2Int ints =
  choice "int2int" [
    ("id", Ex.map (\_ -> id) <$> getDummyEx)
    , ("div", do
        ks <- enumInt ints [2, 3]
        guard $ Ex.all (\k -> k > 0) ks
        pure $ Ex.map (\k -> (\n -> n `div` k)) ks)
    , ("mod", do
        ks <- enumInt ints [2, 3, 4]
        guard $ Ex.all (\k -> k > 1) ks
        pure $ Ex.map (\k -> (\n -> n `mod` k)) ks)
  ]

enumInt2Bool :: (Monad m, HasTrainTest m) => [Choice (Ex Int)] -> SearchT m (Ex (Int -> Bool))
enumInt2Bool ints =
  choice "int2bool" [
    ("eqSmall", do
        ks <- enumInt ints [0, 1, 2]
        pure $ Ex.map (\k -> (\n -> n == k)) ks)
    , ("gtSmall", do
        ks <- enumInt ints [0, 1]
        pure $ Ex.map (\k -> (\n -> n > k)) ks)
  ]
