-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}

module Solver.Tactics.Blast.Candidate where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Util.Imports
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Lib.Grid (Grid)
import Lib.Color (Color)
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
--import Solver.Tactics.Blast.Mask (Mask(..))
import qualified Solver.Tactics.Blast.Goal as BlastGoal -- note the naming
import qualified Solver.Goal as SolverGoal -- note the naming
import qualified Solver.Tactics.Blast.Mask as Mask
import Search.History
import qualified Search.Guess as Guess
import Solver.SolveM

data Candidate = Candidate {
  candidates :: Ex (Grid Color),
  history    :: History
  } deriving (Eq, Ord, Show, Generic)

instance NFData Candidate

isSoundOnMask :: BlastGoal.Goal -> Mask.Mask -> Candidate -> Bool
isSoundOnMask (BlastGoal.Goal inputs outputs reconstructs) (Mask.Mask masks _ _) (Candidate candidates _) =
  flip all (zip4 outputs (Ex.train reconstructs) (Ex.train masks) (Ex.train candidates)) $ \(output, reconstruct, mask, candidate) ->
     Dims.all (Grid.dims output) $ \idx ->
                                     if Grid.get mask idx && not (isJust $ Grid.get reconstruct idx)
                                     then Grid.get output idx == Grid.get candidate idx
                                     else True

computeCandidatesFn :: (SolverGoal.StdGoal -> Synth1M (Ex (Grid Color))) -> SolverGoal.StdGoal -> SolveM [Candidate]
computeCandidatesFn synthCandidatesFn goal = do
  guesses <- liftIO $ runSynth1All (SolverGoal.synthCtx goal) (synthCandidatesFn goal)
  pure $ flip map guesses $ \(Guess.Guess candidates history _ _) ->
    Candidate { candidates = candidates, history = history }
