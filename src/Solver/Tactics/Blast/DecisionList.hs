-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.DecisionList where

import Debug.Trace
import Util.Imports
import qualified Util.List as List
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Data.Ratio
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex

import Solver.Tactics.Blast.Goal (Goal(..))
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate

import Data.Sort (sortBy)
import Lib.Grid (Grid)
import Lib.Color (Color)
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims

-- TODO: PERF make arrays? No idea what the bottlenecks will actually be
rank :: Goal -> Mask.RankingFn -> [Mask] -> [(Mask, Mask.PosteriorFeatures)]
rank goal rankFn masks = runIdentity $ do
  let masksWithFeatures = map (\mask -> (mask, Mask.computePosteriorFeatures goal mask)) masks
  let sortedMasksWithFeatures = flip sortBy masksWithFeatures $ \(m1, f1) (m2, f2) ->
        rankFn (Mask.prior m1, f1) (Mask.prior m2, f2)
  pure $ flip filter sortedMasksWithFeatures $ \(_, posterior) ->
    Mask.nNewCommitments posterior > 0 && Mask.nInputsWithNewCommitment posterior > 1


canReconstructAll :: Goal -> Bool
canReconstructAll (Goal _ _ reconstructs) =
  Ex.all (\reconstruct -> Dims.all (Grid.dims reconstruct) $ isJust . Grid.get reconstruct) reconstructs

extendReconstructs :: Ex (Grid (Maybe Color)) -> Mask -> Candidate -> Ex (Grid (Maybe Color))
extendReconstructs reconstructs (Mask masks _ _) (Candidate candidates _) =
  flip Ex.map (Ex.zip3 reconstructs masks candidates) $ \(reconstruct, mask, candidate) ->
    Grid.fromFunc (Grid.dims reconstruct) $ \idx ->
      case (Grid.get reconstruct idx, Grid.get mask idx) of
        (Just x, _)      -> Just x
        (Nothing, False) -> Nothing
        (Nothing, True)  -> Just $ Grid.get candidate idx

greedyDecision :: Goal -> Mask.RankingFn -> [Mask] -> [Candidate] -> Maybe (Mask, Candidate)
greedyDecision goal rankFn masks candidates = do
  let sortedMasks = rank goal rankFn masks
  flip List.first sortedMasks $ \(mask, posteriorFeatures) -> do
    flip List.first candidates $ \candidate -> do
      guard $ Candidate.isSoundOnMask goal mask candidate
      pure (mask, candidate)

greedyDecisionList :: Int -> Goal -> Mask.RankingFn -> [Mask] -> [Candidate] -> Bool -> ([(Mask, Candidate)], Goal)
greedyDecisionList fuel goal rankFn masks candidates stopOnChange = greedyDecisionListCore fuel goal rankFn masks candidates []
  where
    greedyDecisionListCore :: Int -> Goal -> Mask.RankingFn -> [Mask] -> [Candidate] -> [(Mask, Candidate)] -> ([(Mask, Candidate)], Goal)
    greedyDecisionListCore _ goal _ _ _ acc
      | canReconstructAll goal = (reverse acc, goal)

    greedyDecisionListCore 0 goal _ _ _ acc = (reverse acc, goal) -- succeeds as long as something applied

    greedyDecisionListCore fuel goal rankFn masks candidates acc =
      case greedyDecision goal rankFn masks candidates of
        Nothing                -> (reverse acc, goal)
        Just (mask, candidate) -> --do
          --traceM $ "mask:\n" ++ show mask ++ "candidate:\n" ++ show candidate
          let hasMadeChange = flip Ex.any (Ex.zip3 (Goal.inputs goal) (Mask.masks mask) (Candidate.candidates candidate)) $ \(ig, m, cand) ->
                Dims.any (Grid.dims ig) $ \idx -> not (Grid.get m idx) && (Grid.get ig idx) /= (Grid.get cand idx)

              newGoal = goal { reconstructs = extendReconstructs (Goal.reconstructs goal) mask candidate } in
            if stopOnChange && hasMadeChange then do
              (reverse ((mask, candidate):acc), newGoal)
            else
              greedyDecisionListCore (fuel-1) newGoal rankFn masks candidates ((mask, candidate):acc)
