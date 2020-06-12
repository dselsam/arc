{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ColorBlast.ColorBlast where

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
import Solver.Tactics.Blast.BabyBlasts.ColorBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.BabyBlasts.ColorBlast.Features as Features
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
import Lib.Corner
import qualified Lib.Corner as Corner

import Solver.Tactics.Blast.Util

buildColorBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildColorBlastCtx inputs outputs =
  Synth1Context (length outputs) (length (Ex.test inputs)) True newInts newColors [] [] [] []
  where
    newInts = [] ++
      -- optionally add middle row
      (if flip Ex.all inputs $ \ig -> ((Grid.nRows ig) `mod` 2) == 1
      then [("nRows%2", flip Ex.map inputs $ \ig -> ((Grid.nRows ig) `div` 2))] else []) ++
      -- optionally add middle col
      (if flip Ex.all inputs $ \ig -> ((Grid.nCols ig) `mod` 2) == 1
      then [("nCols%2", flip Ex.map inputs $ \ig -> ((Grid.nCols ig) `div` 2))] else [])

    newColors = []
    newIdxs = [] ++
      -- add corners
      [("topLeftCorner", flip Ex.map inputs $ \ig -> Corner.cornerIdx (Grid.dims ig) TopLeft)
       , ("topRightCorner", flip Ex.map inputs $ \ig -> Corner.cornerIdx (Grid.dims ig) TopRight)
       , ("bottomLeftCorner", flip Ex.map inputs $ \ig -> Corner.cornerIdx (Grid.dims ig) BottomLeft)
       , ("bottomrightCorner", flip Ex.map inputs $ \ig -> Corner.cornerIdx (Grid.dims ig) BottomRight)
       ]


colorBlast :: StdGoal -> SolveM TacticResult
colorBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx (buildColorBlastCtx inputs outputs)
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthColorBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthColorBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  -- FIXME: this currently does not get 2bee17df because of early stopping
  -- do we want a choic point over early stopping?
  Blast.blast 3 False masks candidates reconstructs tacGoal False
