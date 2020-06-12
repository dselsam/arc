-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.SymmetrifyGrid where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Solver.Synth1Context (Synth1Context(..))
import Synth1.Basic
import Lib.Blank (isBlank, blank, nonBlank)
import Solver.Tactics.ImputeBlanks (defaultImputeBlanksGlobalOpts, imputeBlanksGlobal)
import Solver.Tactics.Identity (identity)
import qualified Search.SearchT as SearchT
import Search.SearchT (pop, Result(..))
import Solver.Tactics.RemoveBlockingColor (removeBlockingColor)

import Debug.Trace

symmetrifyGrid :: StdGoal -> SolveM TacticResult
symmetrifyGrid g = do
  TacticResult.Decompose goal@(Goal inputs outputs ctx) _ <-  do
    guard $ all (uncurry Grid.sameDims) (zip (Ex.train $ inputs g) (outputs g))
    choice "symmetrifyGrid"
      [("removeBlockingColor", removeBlockingColor g >>= pop 1 . pure),
       ("pass", pure $ TacticResult.Decompose g pure)]
  result@(TacticResult.Decompose newGoal _) <- imputeBlanksGlobal goal defaultImputeBlanksGlobalOpts
  choice "symmetrifyGrid"
    [("identity", identity newGoal >>= pop 1 . pure ), -- `pop 1 $ identity newGoal` seems to pop regardless
     ("continue", pure result)]
