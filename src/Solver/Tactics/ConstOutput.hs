-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ConstOutput where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import qualified Util.List as List

constOutput :: StdGoal -> SolveM TacticResult
constOutput (Goal inputs outputs ctx) = do
  guard $ List.allSame outputs
  pure $ TacticResult.Guess $ map (\input -> head outputs) (Ex.test inputs)
