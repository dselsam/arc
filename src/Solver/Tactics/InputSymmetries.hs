-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.InputSymmetries where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import Lib.Symmetry (Symmetry (..))
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Synth1.Basic
import Lib.Axis

inputSymmetries goal@(Goal inputs outputs ctx) = do
  runSynth11 ctx $ do
    syms    <- Symmetry.enumReasonableSymmetries
    let union = flip all (zip (Ex.train inputs) outputs) $ \(ig, og) -> Grid.subset ig og

    let f input = do
          g <- liftO $ Symmetry.applyMany syms input
          if union then liftO (Grid.safeUnion input g) else pure g

    newTrainInputs <- flip mapM (zip (Ex.train inputs) outputs) $ \(ig, og) -> do
      newIg <- f ig
      guard $ Grid.subset newIg og
      pure newIg

    guard $ flip all (zip newTrainInputs outputs) (\(newIg, output) -> newIg == output)

    newTestInputs <- mapM f (Ex.test inputs)
    pure $ TacticResult.Guess newTestInputs
