{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ModBlast.ModBlast where

import qualified Data.Maybe as Maybe
import Debug.Trace
import Util.Imports
import Lib.Axis
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
import Solver.Tactics.Blast.BabyBlasts.ModBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.BabyBlasts.ModBlast.Features as Features
import Solver.TacticResult (TacticResult(..))
import qualified Solver.TacticResult as TacticResult

import qualified Search.History as History
import Lib.Blank
import qualified Lib.Grid as Grid
import Solver.SolveM
import Solver.Goal (StdGoal)
import qualified Solver.Goal as TacGoal
import Solver.TacticResult (TacticResult)
import Data.Maybe (fromJust)

import Solver.Synth1Context
import qualified Lib.Axis as Axis
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Dims as Dims
import Lib.Rect
import qualified Lib.Parse as Parse
import Lib.Parse
import qualified Lib.Shape as Shape
import Lib.Shape (Shape)

import Solver.Tactics.Blast.Util

buildModBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildModBlastCtx inputs outputs =
  Synth1Context (length outputs) (length (Ex.test inputs)) True newInts newColors [] [] [] []
  where
    newInts :: [Choice (Ex Int)] = filter (\(_, Ex train test) -> not ((List.allSame train) &&
                                                                  not (List.allSame (train ++ test))))
      [
      ("m - 1", Ex.map (\ig -> (Grid.nRows ig) - 1) inputs),
      ("n - 1", Ex.map (\ig -> (Grid.nCols ig) - 1) inputs)] ++

      (if Ex.all (\ig -> Grid.nNonBlanks ig > 1) inputs then
      [("minOrthoDist", flip Ex.map (Ex.zip inputs allIgNonBlanks) (\(ig, igNonBlanks) ->
          minimum [Axis.dist OrthoDist idx1 idx2 | idx1 <- igNonBlanks, idx2 <- igNonBlanks, idx1 /= idx2])),
      ("maxOrthoDist", flip Ex.map (Ex.zip inputs allIgNonBlanks) (\(ig, igNonBlanks) ->
          maximum [Axis.dist OrthoDist idx1 idx2 | idx1 <- igNonBlanks, idx2 <- igNonBlanks, idx1 /= idx2])),
      ("minDiagDist", flip Ex.map (Ex.zip inputs allIgNonBlanks) (\(ig, igNonBlanks) ->
          minimum [Axis.dist DiagDist idx1 idx2 | idx1 <- igNonBlanks, idx2 <- igNonBlanks, idx1 /= idx2])),
      ("maxDiagDist", flip Ex.map (Ex.zip inputs allIgNonBlanks) (\(ig, igNonBlanks) ->
          maximum [Axis.dist DiagDist idx1 idx2 | idx1 <- igNonBlanks, idx2 <- igNonBlanks, idx1 /= idx2]))] else []) ++

      (if flip Ex.all orthoColorParse (\shapes -> (length shapes) > 1) &&
          flip Ex.all orthoColorParse (\shapes -> flip all shapes (\s -> not (Shape.null s))) then
         [
           ("minDistanceBetweenShapes", flip Ex.map orthoColorParse (\shapes ->
               minimum [fromJust (Shape.minDist DiagDist s1 s2) | s1 <- shapes, s2 <- shapes, s1 /= s2]))
         ]
       else []) ++
      -- optionally add middle row
      (if (flip Ex.all inputs $ \ig -> ((Grid.nRows ig) `mod` 2) == 1) || (flip Ex.all inputs $ \ig -> ((Grid.nRows ig) `mod` 2) == 0)
      then [("nRows%2", flip Ex.map inputs $ \ig -> ((Grid.nRows ig) `div` 2))] else []) ++
      -- optionally add middle col
      (if (flip Ex.all inputs $ \ig -> ((Grid.nCols ig) `mod` 2) == 1) || (flip Ex.all inputs $ \ig -> ((Grid.nCols ig) `mod` 2) == 0)
      then [("nCols%2", flip Ex.map inputs $ \ig -> ((Grid.nCols ig) `div` 2))] else [])

      where

        allIgNonBlanks = Ex.map (\ig -> (Set.toList (Grid.nonBlankIdxs ig))) inputs

        orthoColorParse :: Ex [Shape Color] = flip Ex.map inputs $ \ig ->
          parseScene ig Parse.Options { Parse.kind = Parse.ParseLocalOrtho,   Parse.color = Parse.ParseNoBlanksByColor }

    newColors = []



modBlast :: StdGoal -> SolveM TacticResult
modBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  -- guard we have at least one non blank in each input
  guard $ Ex.all (\ig -> Grid.nNonBlanks ig > 1) inputs

  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx (buildModBlastCtx inputs outputs)
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthModBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthModBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  Blast.blast 4 False masks candidates reconstructs tacGoal True
