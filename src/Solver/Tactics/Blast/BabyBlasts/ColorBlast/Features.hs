{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ColorBlast.Features (synthColorBlastMasks, synthColorBlastCandidates) where

import Util.Imports
import qualified Util.List as List
import Util.List (uncurry4)
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Data.Foldable
import Data.Ratio

import Solver.SolveM
import Solver.Synth1Context
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Search.SearchT
import Search.Guess
import qualified Search.Entry as Entry
import qualified Search.History as History

import Lib.Axis (Axis(..))
import Lib.Direction (Direction(..))
import qualified Lib.Axis as Axis
import Synth1.Synth1Context
import Solver.Goal (Goal(..), StdGoal)
import qualified Solver.Goal as Goal
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Axis as Axis
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.HasElems
import qualified Util.List as List

import Solver.Tactics.Blast.GlobalFeatures

synthColorBlastMasks :: StdGoal -> Synth1M (Ex (Grid Bool))
synthColorBlastMasks goal@(Goal inputs outputs ctx) = do
  (masks :: Ex (Grid Bool)) <- choice "ColorBlast.synthMasks" [
    ("all", allMask goal)
    , ("blank", blankMask goal)
    , ("colorDepend", do
        cs <- Grid.enumRelevantColors inputs outputs
        choice "colorDepend" [
          ("isVal", isValMask goal cs)
          ])
    , ("isIdx", isIdxMask goal)
    , ("onEdge", onEdgeMask goal)
    ]
  phi <- oneOf "negate" [("no",  id), ("yes", not)]
  pure $ flip Ex.map masks $ \mask -> flip Grid.map mask $ \_ b -> phi b



synthColorBlastCandidates :: StdGoal -> Synth1M (Ex (Grid Color))
synthColorBlastCandidates goal@(Goal inputs outputs ctx) =
  choice "synthCandidates" [
    ("blank", blankCandidate goal)
    , ("keep", pure inputs)
    , ("constCand", do
          cs <- Grid.enumRelevantColors inputs outputs
          constCandidate goal cs)
    , ("nearestNonBlank", nearestNonBlankCandidate goal)
    , ("nearestNonSelfVal", nearestNonSelfValCandidate goal)
    , ("nearestNonSelfIdx", nearestNonSelfIdxCandidate goal)
  ]
