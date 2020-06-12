-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.Blast where

import qualified Control.DeepSeq as DeepSeq
import Control.DeepSeq (($!!))
import qualified Data.Maybe as Maybe
import Debug.Trace
import Util.Imports
import qualified Search.History as History
import Util.List as List
import Data.List hiding (partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Synth1.Basic
import Search.SearchT
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Solver.Tactics.Blast.Goal (Goal(..))
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Solver.TacticResult (TacticResult(..))
import qualified Solver.TacticResult as TacticResult

import qualified Search.History as History
import Lib.Blank
import qualified Lib.Grid as Grid
import Solver.SolveM
import Solver.Goal (StdGoal)
import qualified Solver.Goal as TacGoal
import Solver.TacticResult (TacticResult)

import Solver.Synth1Context
import qualified Lib.Axis as Axis
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Dims as Dims
import Lib.Rect

-- TODO: parse global context flag

blast :: Int -> Bool -> [Mask] -> [Candidate] -> Ex (Grid (Maybe Color)) -> StdGoal -> Bool -> SolveM TacticResult
blast blastFuel stopOnChange masks candidates reconstructs tacGoal@(TacGoal.Goal inputs outputs ctx) mustGuess = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  let goal         = Goal inputs outputs reconstructs

  masks        <- pure $!! DeepSeq.force masks
  candidates   <- pure $!! DeepSeq.force candidates
  reconstructs <- pure $!! DeepSeq.force reconstructs

  -- liftIO . traceIO $ "[blast] " ++ show (length masks) ++ " " ++ show (length candidates) ++ " " ++ show (length reconstructs)

  let (history, Goal _ _ newReconstructs) = greedyDecisionList blastFuel goal Mask.defaultRankingFn masks candidates stopOnChange
  let historyString = pretty history
  -- traceM $ "[blast]\n" ++ historyString
  guard . not . null $ history
  newInputs <- flip Ex.mapM (Ex.zip inputs newReconstructs) $ \(input, reconstruct) -> do
    let newInput = Grid.fromFunc (Grid.dims input) $ \idx ->
          case Grid.get reconstruct idx of
            Just x -> x
            Nothing -> Grid.get input idx
    --guard $ input /= newInput
    pure newInput
  -- replaced above guard with below
  -- traceM $ show newInputs
  if mustGuess then do
    guard $ flip all (zip (Ex.train newInputs) outputs) $ \(ig, og) -> ig == og
  else
    guard $ flip any (zip (Ex.toBigList inputs) (Ex.toBigList newInputs)) $ \(input, newInput) -> input /= newInput

  addString historyString $ do
    if mustGuess then pure $ TacticResult.Guess $ Ex.test newInputs
    else pure $ TacticResult.Decompose (tacGoal { TacGoal.inputs = newInputs }) pure

  where
    pretty history = fst $ List.iter history ("", 0) $ \(s, depth) (mask, candidate) -> pure $
      (s ++ (if depth > 0 then "\nELSE " else "") ++ "IF\n" ++ History.showHistory 2 (Mask.history mask) ++ "\nTHEN\n" ++ History.showHistory 2 (Candidate.history candidate), depth+1)
