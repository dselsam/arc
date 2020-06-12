{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.MonsterBlast.Features (synthMonsterBlastMasks, synthMonsterBlastCandidates) where

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

-- TODO(rkruegs123): have at it!
synthMonsterBlastMasks :: StdGoal -> Synth1M (Ex (Grid Bool))
synthMonsterBlastMasks goal@(Goal inputs outputs ctx) = do
  (masks :: Ex (Grid Bool)) <- choice "MonsterBlast.synthMasks" [
    ("all", allMask goal)
    , ("blank", blankMask goal)
    , ("axesBlank", axesBlank goal)
    , ("axesNonBlank", axesNonBlank goal)
    , ("onEdge", onEdgeMask goal)
    , ("isCorner", isCornerMask goal)
    , ("isSurrounded", isSurroundedMask goal)
    , ("flankedByUniformOnAx", flankedByUniformOnAx goal)
    , ("flankedBySpecialOnAx", flankedBySpecialOnAx goal)
    , ("nearestValInAxDirsIsSame", nearestValInAxDirsIsSame goal)
    , ("nonBlankExistsToAxDirs", nonBlankExistsToAxDirs goal)
    , ("nonBlankLineExistsInAxDir", nonBlankLineExistsInAxDir goal)
    , ("colorDepend", do
        cs <- Grid.enumRelevantColors inputs outputs
        choice "colorDepend" [
          ("neighborIsVal", neighborIsVal goal cs),
          ("isVal", isValMask goal cs),
          ("axesHaveVal", axesHaveVal goal cs),
          ("valExistsToAxDirs", valExistsToAxDirs goal cs),
          ("surroundedByValOnAxes", surroundedByValOnAxesMask goal cs),
          ("lineWithValExistsInAxDir", lineWithValExistsInAxDir goal cs)
          ])
    , ("isIdx", isIdxMask goal)
    , ("idxInAnyAx", idxInAnyAxMask goal)
    , ("idxListInAnyAx", anyIdxInAnyAxMask goal)
    , ("idxInAxDir", idxInAxDirMask goal)
    , ("surroundedBySpecialOnAxes", surroundedBySpecialOnAxesMask goal)
    , ("containedInShape", containedInShapeMask goal)
    , ("containedInShapeEnclosingRect", containedInShapeEnclosingRectMask goal)
    , ("containedInAnyShape", containedInAnyShapeMask goal)
    , ("containedInAnyShapeEnclosingRect", containedInAnyShapeEnclosingRectMask goal)
    , ("containedInIdxListMask", containedInIdxListMask goal)
    , ("touchingAnyShapeOrtho", touchingAnyShapeOrthoMask goal)
    , ("touchingAnyShapeDiag", touchingAnyShapeDiagMask goal)
    , ("touchingAnyShapeAll", touchingAnyShapeAllMask goal)
    , ("touchingShapeOrtho", touchingShapeOrthoMask goal)
    , ("touchingShapeDiag", touchingShapeDiagMask goal)
    , ("touchingShapeAll", touchingShapeAllMask goal)
    --, ("flankedByComboOnAx", flankedByComboOnAxMask goal)
    , ("indirect", do
        intGrids :: Ex (Grid Int) <- enumIndex2Int goal
        boolGrids :: (Ex (Grid Bool)) <- choice "MonsterBlast.int2boolMethod" [
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
    , ("indirectMaybe", do
        intGrids :: Ex (Grid (Maybe Int)) <- enumIndex2MaybeInt goal
        boolGrids :: (Ex (Grid Bool)) <- choice "MonsterBlast.int2boolMethod" [
          ("int2boolFn", do
              int2ints :: Ex (Int -> Int) <- enumInt2Int (ctxInts ctx)
              int2bools :: Ex (Int -> Bool) <- enumInt2Bool (ctxInts ctx)
              pure $ flip Ex.map (Ex.zip3 intGrids int2ints int2bools) $ \(intGrid, int2int, int2bool) -> do
                Grid.fromFunc (Grid.dims intGrid) $ \idx ->
                  case Grid.get intGrid idx of
                    Nothing -> False
                    Just val -> int2bool (int2int val)),
          ("int2boolExtreme", do
              guard $ flip Ex.all intGrids (\intG -> Dims.any (Grid.dims intG) $ \idx -> isJust (Grid.get intG idx))
              (extremeVals :: Ex (Maybe Int)) <- choice "extreme" [
                ("maximum", pure $ flip Ex.map intGrids (\intG -> Vector.maximum (Grid.gridData intG))),
                -- if we don't do this it will be Nothing
                ("minimum", pure $ flip Ex.map intGrids (\intG ->
                     minimum $ filter (\mVal -> isJust mVal) (Grid.toList intG)))
                ]
              -- implicitly turns all nothings to false because xVal will always be a Just
              pure $ flip Ex.map (Ex.zip intGrids extremeVals) (\(intG, xVal) ->
                  flip Grid.map intG (\idx val -> if val == xVal then True else False)))
          ]
        pure $ boolGrids)
    ]
  phi <- oneOf "negate" [("no",  id), ("yes", not)]
  pure $ flip Ex.map masks $ \mask -> flip Grid.map mask $ \_ b -> phi b




-- TODO(rkruegs123): have at it!
synthMonsterBlastCandidates :: StdGoal -> Synth1M (Ex (Grid Color))
synthMonsterBlastCandidates goal@(Goal inputs outputs ctx) =
  choice "synthCandidates" [
    ("blank", blankCandidate goal)
    , ("keep", pure inputs)
    , ("constCand", do
          cs <- Grid.enumRelevantColors inputs outputs
          constCandidate goal cs)
    , ("axMax", axMaxCandidate goal)
    , ("nearestValInAxDir", nearestValInAxDirCandidate goal)
    , ("furthestValInAxDir", furthestValInAxDirCandidate goal)
    , ("nearestNonBlank", nearestNonBlankCandidate goal)
    , ("nearestNonSelfVal", nearestNonSelfValCandidate goal)
    , ("neighborVal", neighborVal goal)
    , ("nearestNonSelfIdx", nearestNonSelfIdxCandidate goal)
    , ("reflect", do
       ax <- enumVals
       pure $ flip Ex.map inputs $ \ig -> Grid.reflectAround ig ax)
  ]


----------------------
-- Int
----------------------

-- FIXME: we are recomputing all the consts for each (Ex Int)
enumInt :: (Monad m, HasTrainTest m) => [Choice (Ex Int)] -> [Int] -> SearchT m (Ex Int)
enumInt ints consts =
  choice "enumInt" [
    ("const", do
      x <- oneOf "Int.enumConst" $ flip Prelude.map consts $ \k -> (show k, k)
      Ex.map (\_ -> x) <$> getDummyEx)
    , ("ctx", oneOf "ctx" ints)
  ]

enumInt2Int :: (Monad m, HasTrainTest m) => [Choice (Ex Int)] -> SearchT m (Ex (Int -> Int))
enumInt2Int ints =
  choice "int2int" [
    ("id", Ex.map (\_ -> id) <$> getDummyEx)
    , ("div", do
        ks <- enumInt ints [2, 3]
        guard $ Ex.all (\k -> k > 0) ks
        pure $ Ex.map (\k -> (\n -> n `div` k)) ks)
    , ("mod", do
        ks <- enumInt ints [2, 3]
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
