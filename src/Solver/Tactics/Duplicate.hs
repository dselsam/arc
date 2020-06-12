-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Duplicate where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import Lib.Blank
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult

---------------
-- Duplicate
---------------
-- Requires:
--   - Each of the test inputs equals one of the train inputs
-- Considers:
--   - Guesses the matching train output for each test input

duplicate :: StdGoal -> SolveM TacticResult
duplicate (Goal inputs outputs ctx) = do
  -- heuristic guard
  guard $ flip any inputs $ \input -> Grid.nDistinctVals nonBlank input > 0
  foundOutputs <- liftO $ flip mapM (Ex.test inputs) $ flip elemIndex (Ex.train inputs)
  pure $ TacticResult.Guess $ Prelude.map (outputs !!) foundOutputs
