{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.AxesBlast.AxesBlast where

import Data.List hiding (partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Vector.Unboxed as Vector

import Debug.Trace

import Util.List as List
import Util.Imports

import Search.SearchT
import qualified Search.History as History
import qualified Search.History as History

import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex

import Solver.Tactics.Blast.Goal (Goal(..))
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import Solver.Tactics.Blast.BabyBlasts.AxesBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.BabyBlasts.AxesBlast.Features as Features
import Solver.TacticResult (TacticResult(..))
import qualified Solver.TacticResult as TacticResult
import Solver.SolveM
import Solver.Goal (StdGoal)
import qualified Solver.Goal as TacGoal
import Solver.TacticResult (TacticResult)
import Solver.Synth1Context
import Solver.Tactics.Blast.GlobalFeatures

import Lib.Blank
import qualified Lib.Grid as Grid
import qualified Lib.Axis as Axis
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Dims as Dims
import Lib.Rect
import Solver.Tactics.Blast.Util



buildAxesBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildAxesBlastCtx inputs outputs =
  Synth1Context (length outputs) (length (Ex.test inputs)) True newInts newColors [] [] [] []
  where
    newInts :: [Choice (Ex Int)] = filter (\(_, Ex train test) -> not ((List.allSame train) &&
                                                                  not (List.allSame (train ++ test))))
      [
      ("m - 1", Ex.map (\ig -> (Grid.nRows ig) - 1) inputs),
      ("n - 1", Ex.map (\ig -> (Grid.nCols ig) - 1) inputs)
      ]
    newColors = []



axesBlast :: StdGoal -> SolveM TacticResult
axesBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx (buildAxesBlastCtx inputs outputs)
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthAxesBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthAxesBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  -- FIXME: this currently does not get 2bee17df because of early stopping
  -- do we want a choic point over early stopping?
  Blast.blast 3 False masks candidates reconstructs tacGoal False
