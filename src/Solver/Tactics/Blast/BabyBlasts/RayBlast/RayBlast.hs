{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.RayBlast.RayBlast where

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
import Solver.Tactics.Blast.BabyBlasts.RayBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.BabyBlasts.RayBlast.Features as Features
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

import Solver.Tactics.Blast.Util

buildRayBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildRayBlastCtx inputs outputs =

  Synth1Context (length outputs) (length (Ex.test inputs)) True newInts newColors [] [] [] []
  where
    newInts :: [Choice (Ex Int)] = filter (\(_, Ex train test) -> not ((List.allSame train) &&
                                                                  not (List.allSame (train ++ test))))
      [
      ("m - 1", Ex.map (\ig -> (Grid.nRows ig) - 1) inputs),
      ("n - 1", Ex.map (\ig -> (Grid.nCols ig) - 1) inputs)
      ]
    newColors = []


rayBlast :: StdGoal -> SolveM TacticResult
rayBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx (buildRayBlastCtx inputs outputs)
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthRayBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthRayBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  Blast.blast 4 False masks candidates reconstructs tacGoal False
