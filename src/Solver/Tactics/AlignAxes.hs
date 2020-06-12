-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.AlignAxes where

import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import Lib.Axis
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import qualified Lib.Dims as Dims
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Search.SearchT

---------------
-- AlignAxes
---------------
-- Requires:
--   - some of the inputs have more rows, others have more columns
-- Considers:
--   - rotating some of them so that all "face in the same direction"

alignAxesLines :: StdGoal -> SolveM TacticResult
alignAxesLines goal@(Goal inputs outputs ctx) = do
  let axisThreshold = 0.9-- <- oneOf "axisThreshold" [("0.9", 0, 0.9)]
  axes :: Ex Axis <- flip Ex.mapM inputs $ \input -> do
    let hasHLines = not . null $ Grid.fuzzyHorizontalLines input axisThreshold
    let hasVLines = not . null $ Grid.fuzzyVerticalLines input axisThreshold
    guard $ xor hasHLines hasVLines
    pure $ if hasHLines then Horizontal else Vertical
  guard $ not . List.allSame $ Ex.toBigList axes
  let flips = Ex.map ((\b -> (b, b)) . (not . (==Horizontal))) axes
  alignAxesCore flips goal

alignAxesDims :: StdGoal -> SolveM TacticResult
alignAxesDims goal@(Goal inputs outputs ctx) = choice "alignAxesDims" [
  ("checkLines", do
      for_ inputs $ \input -> do
        let axisThreshold = 0.95
        let hasHLines = not . null $ Grid.fuzzyHorizontalLines input axisThreshold
        let hasVLines = not . null $ Grid.fuzzyVerticalLines input axisThreshold
        guard $ xor hasHLines hasVLines
      pop 1 $ deadend ""),
  ("alignDims", do
      -- TODO: confirm that we don't go in circle, or that if we do, we get cache hits
      flips :: Ex (Bool, Bool) <- choice "alignAxes" [
        ("skinnyFatInputs",        skinnyFatInputs goal)
        , ("skinnyInputsFatOutputs", skinnyInputsFatOutputs goal)
        ]

      alignAxesCore flips goal)
  ]

    where
      skinnyFatInputs :: StdGoal -> SolveM (Ex (Bool, Bool))
      skinnyFatInputs (Goal inputs outputs ctx) = do
        let inputDims = Ex.map Grid.dims inputs
        -- Note: this fires on 272f95fa before the partition though,
        -- even though there are no test inputs that are getting flipped.
        -- We could replace `Ex.toBigList` with `Ex.train`, but I tentatively prefer
        -- putting partition before axisAlign instead.
        guard . not . null . filter Dims.isSkinny $ Ex.toBigList inputDims
        guard . not . null . filter Dims.isFat $ Ex.toBigList inputDims
        pure $ Ex.map (\dims -> (Dims.isSkinny dims, Dims.isSkinny dims)) inputDims

      skinnyInputsFatOutputs :: StdGoal -> SolveM (Ex (Bool, Bool))
      skinnyInputsFatOutputs (Goal inputs outputs ctx) = do
        guard $ all isSwapped (zip (train inputs) outputs)
        pure $ Ex.map (\_ -> (True, False)) inputs
        where
          isSwapped = \(input, output) ->
            ((Dims.isSkinny $ Grid.dims input) && (Dims.isFat $ Grid.dims output))
            || ((Dims.isFat $ Grid.dims input) && (Dims.isSkinny $ Grid.dims output))


alignAxesCore :: Ex (Bool, Bool) -> StdGoal -> SolveM TacticResult
alignAxesCore flips goal@(Goal inputs outputs ctx) = do
  flips <- oneOf "flips" [(show flips, flips)]

  let f b0 (g, (b1, b2)) = if (b0 && b1) || (not b0 && b2) then Grid.transpose g else g
  let newInputs   = flip Ex.map (Ex.zip inputs flips) (f True)
  let newOutputs  = flip map (zip outputs (Ex.train flips)) (f False)
  let reconstruct guesses = do
        pure $ flip map (zip guesses (Ex.test flips)) (f False)
  pure $ Decompose (Goal newInputs newOutputs ctx) reconstruct
