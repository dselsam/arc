-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ExactSubgrid where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import qualified Lib.Rect as Rect
import Lib.Rect (Rect(Rect))
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Solver.Tactics.GuessDims
import Synth1.Basic
import Search.SearchT

---------------
-- ExactSubgrid
---------------
-- Requires:
--   - For each training example, the output appears as a subgrid of the input.
-- Considers:
--   - All possible sets of matching indices for each example
--   - Each index being (i or <m> - i, j or <n> - j)
-- TODO:
--   - Could use more sophisticated features
--     - grid level: nDistinctColors, context nats
--     - parse aware: enclosing rect of biggest shape?
--   - Could in principle allow an arbitrary expression

-- TODO: this is special-cased but general arithmetic module could handle it
enumIntersection :: ForTrain [Index] -> Synth1M Index
enumIntersection candidates = do
  let (first:rest) = candidates
  let intersection = List.iter rest (Set.fromList first) $ \acc candidates ->
        pure $ Set.intersection acc (Set.fromList candidates)
  enumListElems $ Set.toList intersection

synthGrid2Index :: Ex (Grid Color) -> ForTrain [Index] -> Synth1M (ForTest Index)
synthGrid2Index inputs candidates = do
  revRows <- oneOf "revRows" [("no", False), ("yes", True)]
  revCols <- oneOf "revCols" [("no", False), ("yes", True)]
  let revIndex (Dims m n) (Index i j) = Index (if revRows then m - i else i) (if revCols then n - j else j)
  let revCandidates = flip map (zip (Ex.train inputs) candidates) $ \(input, candidates) -> map (revIndex . Grid.dims $ input) candidates
  idx <- enumIntersection revCandidates
  pure $ map (\input -> revIndex (Grid.dims input) idx) (Ex.test inputs)

exactSubgrid :: StdGoal -> SolveM TacticResult
exactSubgrid goal@(Goal inputs outputs ctx) = do
  testDims <- synthDims goal
  guard $ flip Ex.all (Ex.zip inputs (Ex (map Grid.dims outputs) testDims))  $ \(input, Dims m n) ->
    Grid.nRows input >= m || Grid.nCols input >= n
  guard $ flip Ex.any (Ex.zip inputs (Ex (map Grid.dims outputs) testDims))  $ \(input, Dims m n) ->
    Grid.nRows input > m || Grid.nCols input > n
  let candidates = flip map (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Grid.findSubgrids input (Grid.dims output) (== output)
  idxs <- runSynth11 ctx $ synthGrid2Index inputs candidates
  for_ (zip3 testDims idxs (Ex.test inputs)) $ \(dims, idx, input) -> do
    let guessRect = Rect idx dims
    let inputRect = Rect.fromDims $ Grid.dims input
    unless (Rect.contains2nd inputRect guessRect) $ do
      liftIO . traceIO $ "[exactSubgrid] OOB: " ++ show guessRect ++ " not contained in " ++ show inputRect
      deadend ""
  let guesses = flip map (zip3 testDims idxs (Ex.test inputs)) $ \(dims, idx, input) ->
        Grid.getSubgridUnsafe input dims idx
  pure $ TacticResult.Guess guesses
