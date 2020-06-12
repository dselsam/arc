-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Identity where

import Util.Imports
import Util.List (uncurry3)
import Solver.SolveM
import Solver.Goal
import Synth.Ex (Ex)
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult

---------------
-- Identity
---------------
-- Requires:
--   - Each of the training inputs equals each of the training outputs.
-- Considers:
--   - Guesses the test inputs.

identity :: StdGoal -> SolveM TacticResult
identity (Goal inputs outputs ctx) = do
  guard $ all (uncurry (==)) $ zip (Ex.train inputs) outputs
  pure $ TacticResult.Guess $ Ex.test inputs
