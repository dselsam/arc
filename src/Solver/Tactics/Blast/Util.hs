-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.Util where

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
import Lib.Shape (Shape)
import Lib.Rect (Rect)
import qualified Lib.Shape as Shape
import qualified Lib.Rect as Rect
import qualified Lib.Axis as Axis
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.HasElems

import qualified Util.List as List


reduceMasksOr :: [Ex (Grid Bool)] -> Ex (Grid Bool)
reduceMasksOr allMasks =
  List.reduce (\ex1 ex2 ->
            flip Ex.map (Ex.zip ex1 ex2) (\(g1, g2) -> Grid.mapBinOp (Blank.orD True) g1 g2)) id allMasks


reduceMasksAnd :: [Ex (Grid Bool)] -> Ex (Grid Bool)
reduceMasksAnd allMasks =
  List.reduce (\ex1 ex2 ->
            flip Ex.map (Ex.zip ex1 ex2) (\(g1, g2) -> Grid.mapBinOp (Blank.andD True) g1 g2)) id allMasks


-- filter out dangerous values in the ctx: those that are the same for the train, but differ on test
filterUnsafeChoices :: (Eq a) => [Choice (Ex a)] -> [Choice (Ex a)]
filterUnsafeChoices choices =
  flip filter choices
    $ \(_, Ex train test) -> not $ (List.allSame train) && not (List.allSame (train ++ test))

makeBlastCtxSafe :: Synth1Context -> Synth1Context
makeBlastCtxSafe (Synth1Context nTrain nTest hf ints colors idxs idxLists shapes shapeLists) =
  Synth1Context nTrain nTest hf
    (filterUnsafeChoices ints)
    (filterUnsafeChoices colors)
    (filterUnsafeChoices idxs)
    (filterUnsafeChoices idxLists)
    (filterUnsafeChoices shapes)
    (filterUnsafeChoices shapeLists)
