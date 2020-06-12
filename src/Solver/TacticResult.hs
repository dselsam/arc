-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.TacticResult where

import Util.Imports
import Synth.Ex
import Lib.Color
import Lib.Grid
import Solver.Synth1Context
import Solver.Goal
import Solver.SolveM

type Reconstruct a b = ForTest a -> MaybeT IO (ForTest b)
type StdReconstruct = Reconstruct (Grid Color) (Grid Color)

data TacticResult = Guess (ForTest (Grid Color))
                  | Decompose StdGoal StdReconstruct
