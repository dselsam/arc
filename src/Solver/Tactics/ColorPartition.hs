-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ColorPartition where

import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import qualified Data.Maybe as Maybe
import qualified Solver.Goal
import Search.SearchT
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Index as Index
import qualified Lib.Rect as Rect
import qualified Data.Map as Map
import qualified Util.Map as Map
import Lib.Axis
import Lib.Index (Index(Index))
import Search.Guess (Guess(Guess))
import qualified Search.Guess as Guess
import Search.History (History)
import qualified Search.History as History
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color
import Lib.Blank
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import qualified Lib.Parse as Parse
import qualified Lib.AlignShapes as AlignShapes
import Solver.Parse (getParseResult, ParseResult(ParseResult))
import Synth1.Basic
import Solver.Goal
import Synth.Int2Bool
import Synth.Bool
import Synth.Core
import Synth.EagerFeatures
import Synth.LazyFeatures
import Synth.Sequence
import Search.DFS
import Synth.Spec
import qualified Data.Set as Set
import qualified Synth.Spec as Spec
import qualified Lib.Shape as Shape
import qualified Solver.Tactics.Blast.Goal as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import Solver.Tactics.Blast.Mask (Mask(Mask))
import qualified Solver.Tactics.Blast.Mask as Mask
import Solver.Tactics.Blast.Candidate (Candidate(Candidate))
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Solver.Tactics.DyeInputs (synthG2C)
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import qualified Util.Int as Int
import qualified Lib.BGrid as Box
import qualified Data.List as List
import Solver.Goal

colorPartition :: StdGoal -> SolveM TacticResult
colorPartition goal@(Goal inputs outputs ctx) = do
  -- motivated by 1bfc4729 (case1) and e7dd (case2)
  withoutColors :: ForTest (Grid Color) <-
        if flip all outputs $ \output -> Grid.sameBlanks (head outputs) output
        then pure $ replicate (length (Ex.test inputs)) (head outputs)
        else if flip all (zip (Ex.train inputs) outputs) $ \(input, output) -> Grid.sameBlanks input output
             then pure $ Ex.test inputs
             else deadend ""

  -- TODO: could synthesize these dims instead of requiring they all be the same
  outerDims :: Dims <- liftO $ detectColorPartitionOuterDims outputs

  pOutputs   <- liftO . flip mapM outputs  $ Grid.partitionEvenOuterDims outerDims
  newOutputs <- liftO $ flip mapM pOutputs $ \pOutput -> Grid.fromFuncM outerDims $ \oIdx -> do
    let vals = Grid.distinctVals nonBlank (Box.get pOutput oIdx)
    guard $ Set.size vals == 1
    pure $ Set.elemAt 0 vals

  pTests <- liftO . flip mapM withoutColors $ Grid.partitionEvenOuterDims outerDims
  let reconstruct guesses = MaybeT . pure . flip mapM (zip pTests guesses) $ \(pTest, guess) -> do
        unless (Grid.dims guess == Box.dims pTest) $
          traceM $ "colorPartitionReconstruct: " ++ show (Grid.dims guess, Box.dims pTest)
        guard $ Grid.dims guess == Box.dims pTest
        let pGuess :: Box.Grid (Grid Color) = Box.fromFunc outerDims $ \oIdx ->
              Grid.map (\_ x -> if nonBlank x then Grid.get guess oIdx else blank) (Box.get pTest oIdx)
        Grid.unpartitionEven pGuess

  pure $ TacticResult.Decompose (Goal inputs newOutputs ctx) reconstruct

  where
    detectColorPartitionOuterDims :: ForTrain (Grid Color) -> Maybe Dims
    detectColorPartitionOuterDims outputs = do
      -- lower numbers correspond to fewer colors to predict
      let outerDimsToTry = List.sortOn (uncurry (*)) $ do
            m <- Int.allCommonDivisors . map Grid.nRows $ outputs
            n <- Int.allCommonDivisors . map Grid.nCols $ outputs
            pure (m, n)
      flip List.first outerDimsToTry $ \(m, n) -> do
        guard $ m > 1 || n > 1
        let outerDims = Dims m n
        pOutputs <- mapM (Grid.partitionEvenOuterDims outerDims) outputs
        guard $ flip all pOutputs $ \pOutput -> Dims.all (Box.dims pOutput) $ \idx ->
          Grid.nDistinctVals nonBlank (Box.get pOutput idx) <= 1
        pure $ outerDims
