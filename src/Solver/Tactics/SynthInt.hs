-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.SynthInt where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Lib.Dims (Dims (Dims))
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import qualified Data.Map as Map
import Lib.Index (Index (Index))
import Synth1.Arith
import Search.SearchT
import Lib.Blank
import qualified Lib.Parse as Parse
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Solver.Parse
import Solver.Tactics.GuessDims
import qualified Synth.Spec as Spec
import qualified Lib.Shape as Shape
import Search.DFS
import Synth.Basic
import Solver.Parse
import Synth.Core
import Synth.LazyFeatures
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.LazyFeatures as LazyFeatures
import Synth1.Basic
import Synth.Int2Bool
import Synth.Bool2Bool
import Synth.Sequence
import Solver.Synth1Context (ctxInts, ctxColors)

-- TODO: 1fad071e
synthInt :: StdGoal -> SolveM TacticResult
synthInt goal@(Goal inputs outputs ctx) = find1 "synthInt" $ do
  guard $ List.allSame (map Grid.dims outputs)
  guard $ all ((==1) . Grid.nCols) outputs || all ((==1) . Grid.nRows) outputs
  guard $ any ((>1)  . Grid.nCols) outputs || any ((>1)  . Grid.nRows) outputs

  intLabels :: ForTrain Int <- flip mapM outputs $ \output -> do
    deadend ""

  deadend ""
