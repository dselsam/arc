-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Upscale where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import Synth1.Arith
import Solver.Tactics.GuessDims

upscale :: StdGoal -> SolveM TacticResult
upscale goal@(Goal inputs outputs ctx) = do
  testDims <- synthDims goal
  diffs :: Ex Dims <- flip Ex.mapM (Ex.zip (Ex.map Grid.dims inputs) (Ex (map Grid.dims outputs) testDims)) $ \(Dims ir ic, Dims or oc) -> do
    guard $ or `rem` ir == 0
    guard $ oc `rem` ic == 0
    pure $ Dims (or `div` ir) (oc `div` ic)

  -- TODO: guard most?
  guard $ flip Ex.any diffs $ \(Dims r c) -> r > 1 || c > 1

  upFn :: Grid Color -> Dims -> Grid Color <- choice "upscale" [
    ("upscale", pure $ \g dims -> Maybe.fromJust $ Grid.unpartitionEven $ Grid.upscale g dims),
    ("tile",    pure $ \g dims -> Maybe.fromJust $ Grid.unpartitionEven $ Grid.tile g dims)
    ]

  let newInputs :: Ex (Grid Color) = Ex.map (uncurry upFn) (Ex.zip inputs diffs)
  -- TODO: too strict!! But we don't want floats.
  guard $ flip all (zip (Ex.train newInputs) outputs) $ \(input, output) ->
    Grid.subset input output || Grid.sameBlanks input output

  pure $ TacticResult.Decompose (goal { inputs = newInputs }) pure
