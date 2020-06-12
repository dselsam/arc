{-# LANGUAGE ScopedTypeVariables #-}
module Solver.Tactics.Blast.MonsterBlast.MonsterBlast where

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
import Solver.Tactics.Blast.MonsterBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.MonsterBlast.Features as Features
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

-- import baby blast context builders
import Solver.Tactics.Blast.BabyBlasts.AxesBlast.AxesBlast (buildAxesBlastCtx)
import Solver.Tactics.Blast.BabyBlasts.ColorBlast.ColorBlast (buildColorBlastCtx)
import Solver.Tactics.Blast.BabyBlasts.ModBlast.ModBlast (buildModBlastCtx)
import Solver.Tactics.Blast.BabyBlasts.NeighborBlast.NeighborBlast (buildNeighborBlastCtx)
import Solver.Tactics.Blast.BabyBlasts.RayBlast.RayBlast (buildRayBlastCtx)
import Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.ShapeFeaturesBlast (buildShapeFeatureBlastCtx)

import Solver.Tactics.Blast.Util


-- FIXME: right now, enumRelevantColors still handles colors
buildMonsterBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildMonsterBlastCtx inputs outputs =
  Synth1Context (length outputs) (length (Ex.test inputs)) True
    (newInts ++ (ctxInts allBabyBlastCtxs))
    (newColors ++ (ctxColors allBabyBlastCtxs))
    (newIdxs ++ (ctxIdxs allBabyBlastCtxs))
    (newIdxLists ++ (ctxIdxLists allBabyBlastCtxs))
    (newShapes ++ (ctxShapes allBabyBlastCtxs))
    (newShapeLists ++ (ctxShapeLists allBabyBlastCtxs))

  where

    allBabyBlastCtxs = mergeAllSynth1Contexts $ flip Prelude.map
      [buildAxesBlastCtx, buildColorBlastCtx, buildModBlastCtx, buildNeighborBlastCtx,
       buildRayBlastCtx, buildShapeFeatureBlastCtx]
      (\builder -> builder inputs outputs)

    newInts :: [Choice (Ex Int)] =
      [
      ("m - 1", Ex.map (\ig -> (Grid.nRows ig) - 1) inputs),
      ("n - 1", Ex.map (\ig -> (Grid.nCols ig) - 1) inputs),
      ("nDistinctVals", Ex.map (\ig -> Grid.nDistinctVals (\_ -> True) ig) inputs),
      ("nDistinctNonBlankVals", Ex.map (\ig -> Grid.nDistinctVals nonBlank ig) inputs)
      ] ++
      -- optionally add middle row
      (if (flip Ex.all inputs $ \ig -> ((Grid.nRows ig) `mod` 2) == 1) || (flip Ex.all inputs $ \ig -> ((Grid.nRows ig) `mod` 2) == 0)
      then [("nRows%2", flip Ex.map inputs $ \ig -> ((Grid.nRows ig) `div` 2))] else []) ++
      -- optionally add middle col
      (if (flip Ex.all inputs $ \ig -> ((Grid.nCols ig) `mod` 2) == 1) || (flip Ex.all inputs $ \ig -> ((Grid.nCols ig) `mod` 2) == 0)
      then [("nCols%2", flip Ex.map inputs $ \ig -> ((Grid.nCols ig) `div` 2))] else [])

    newColors = []
    newIdxs = []
    newIdxLists = []
    newShapes = []
    newShapeLists = []



monsterBlast :: StdGoal -> SolveM TacticResult
monsterBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx $ buildMonsterBlastCtx inputs outputs
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthMonsterBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthMonsterBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  Blast.blast 8 False masks candidates reconstructs tacGoal True
