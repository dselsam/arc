-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.Goal where

import Util.Imports
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Lib.Grid (Grid)
import Lib.Color (Color)

-- TODO: make (doubly) polymorphic in Color?
data Goal = Goal {
  inputs       :: Ex (Grid Color),
  outputs      :: ForTrain (Grid Color),
  reconstructs :: Ex (Grid (Maybe Color))
  }
