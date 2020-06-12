{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.NeighborBlast.Features (synthNeighborBlastMasks, synthNeighborBlastCandidates) where

import qualified Data.Vector.Unboxed as Vector
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
import Lib.Index
import qualified Lib.Axis as Axis
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.HasElems
import qualified Util.List as List

import Solver.Tactics.Blast.GlobalFeatures

synthNeighborBlastMasks :: StdGoal -> Synth1M (Ex (Grid Bool))
synthNeighborBlastMasks goal@(Goal inputs outputs ctx) = do
  (masks :: Ex (Grid Bool)) <- choice "NeighborBlast.synthMasks" [
    ("all", allMask goal)
    , ("blank", blankMask goal)
    , ("isSurrounded", isSurroundedMask goal)
    , ("colorDepend", do
        cs <- Grid.enumRelevantColors inputs outputs
        choice "colorDepend" [
          ("isVal", isValMask goal cs),
          ("neighborIsVal", neighborIsVal goal cs)])
    , ("indirect", do
        intGrids :: Ex (Grid Int) <- choice "NeighborBlast.index2int" [
          ("row", rowMask goal)
          , ("col", colMask goal)
          , ("nNeighbors", nNeighborsMask goal)
          , ("nNeighborColors", nNeighborColorsMask goal)
          ]
        boolGrids :: (Ex (Grid Bool)) <- choice "NeighborBlast.int2boolMethod" [
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


synthNeighborBlastCandidates :: StdGoal -> Synth1M (Ex (Grid Color))
synthNeighborBlastCandidates goal@(Goal inputs outputs ctx) =
  choice "synthCandidates" [
    ("blank", blankCandidate goal)
    , ("keep", pure inputs)
    , ("constCand", do
          cs <- Grid.enumRelevantColors inputs outputs
          constCandidate goal cs)
    -- leads to bad guesses, but here if we need it
    -- , ("neighborVal", neighborVal goal)
    -- TODO: Add majority neighbor color
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
    -- no div or mod for now
    ("id", Ex.map (\_ -> id) <$> getDummyEx)
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
