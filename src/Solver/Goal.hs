-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Goal where

import Synth.Ex
import Lib.Color
import Lib.Grid
import qualified Lib.BGrid as Box
import Lib.Dims
import Solver.Synth1Context
import Synth.Spec

-- type Goal a b = ESpecType (Synth1Context, Ex a) b

data Goal a b = Goal {
  inputs     :: Ex a,
  outputs    :: ForTrain b,
  synthCtx   :: Synth1Context
  } deriving (Eq, Ord, Show)

type StdGoal   = Goal (Grid Color) (Grid Color)
type GoalGG2GG = Goal (Box.Grid (Grid Color)) (Box.Grid (Grid Color))
type GoalGG2G  = Goal (Box.Grid (Grid Color)) (Grid Color)
