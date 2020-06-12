-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.SanityCheck where

import Search.SearchT
import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Util.List as List
import Lib.Grid (Grid)
import Lib.Color (Color)
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult

sanityCheckGoal :: StdGoal -> SolveM ()
sanityCheckGoal goal = do
  rightNumbersOfThings goal
  guardGoalIsFunctional goal
  checkCache goal

  where
    rightNumbersOfThings :: StdGoal -> SolveM ()
    rightNumbersOfThings (Goal inputs outputs _) = do
      -- TODO: print a warning
      guard . not . null $ Ex.train inputs
      guard $ length (Ex.train inputs) == length outputs
      guard . not . null $ Ex.test inputs

    guardGoalIsFunctional :: StdGoal -> SolveM ()
    guardGoalIsFunctional (Goal inputs outputs _) = do
      _ <- List.iterM (zip (Ex.train inputs) outputs) Map.empty $ \acc (input, output) ->
        case Map.lookup input acc of
          Nothing -> pure $ Map.insert input output acc
          Just output0 -> do { guard (output0 == output); pure acc }
      pure ()

    checkCache goal = do
      cache <- visitedGoals <$> lift get
      case Set.member goal cache of
        False -> lift $ modify $ \s -> s { visitedGoals = Set.insert goal cache }
        True  -> do
          --withHistory $ \history -> liftIO . traceIO $ "[sanityCheckGoal] goal found in cache\n" ++ show history
          deadend ""

sanityCheckGuesses :: StdGoal -> ForTest (Grid Color) -> SolveM ()
sanityCheckGuesses goal guesses = pure ()
