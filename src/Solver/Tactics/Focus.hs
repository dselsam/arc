-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Focus where

import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Rect as Rect
import Solver.Synth1Context (ctxHaveFocused)
import Lib.Axis
import Lib.Direction (Direction(..))
import Lib.Index (Index(Index))
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import qualified Lib.Dims as Dims
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Solver.Tactics.GuessDims
import Search.DFS

-- TODO: new experiment, may be bad
data FocusOptions = FocusOptions {
  minimumRatioI  :: Float,
  minimumRatioIO :: Float
  } deriving (Eq, Ord, Show)

defaultFocusOptions :: FocusOptions
defaultFocusOptions = FocusOptions { minimumRatioI = 0.70, minimumRatioIO = 0.80 }

focus :: StdGoal -> SolveM TacticResult
focus goal = choice "focus" [
  ("nonBlankI",  focusNonBlankI goal),
  ("nonBlankIO", focusNonBlankIO goal)
  ]

focusNonBlankI :: StdGoal -> SolveM TacticResult
focusNonBlankI goal@(Goal inputs outputs synthCtx) = do
  -- TODO: too strong?
  guard . flip any (zip (Ex.train inputs) outputs) $ (not . uncurry Grid.sameDims)
  rects <- liftO $ Ex.mapM Grid.nonBlankRect inputs
  guard $ flip Ex.any (Ex.zip inputs rects) $ \(input, rect) -> Rect.fromDims (Grid.dims input) /= rect

  -- TODO: guard most?
  unless (flip any (zip (Ex.train rects) outputs) $ \(rect, output) -> Rect.dims rect == Grid.dims output) $
    guard $ flip Ex.any (Ex.zip rects inputs) $ \(rect, input) ->
      fromIntegral (Dims.nCells (Rect.dims rect)) < fromIntegral (Dims.nCells (Grid.dims input)) * minimumRatioI defaultFocusOptions

  let newInputs = flip Ex.map (Ex.zip rects inputs) $ \(rect, input) -> Grid.getRect input rect
  let newGoal = goal { inputs = newInputs, synthCtx = synthCtx { ctxHaveFocused = True } }

  couldSynthDims  <- canSynthDims goal
  nowCanSynthDims <- canSynthDims newGoal
  guard $ couldSynthDims <= nowCanSynthDims

  pure $ TacticResult.Decompose newGoal pure

focusNonBlankIO :: StdGoal -> SolveM TacticResult
focusNonBlankIO goal@(Goal inputs outputs ctx) = find1 "focusNonBlankIO" $ do
  -- (top, bottom, left, right)
  crops@(top, bottom, left, right) <- List.iterM (zip (Ex.train inputs) outputs) (True, True, True, True) $ \(top, bottom, left, right) (input, output) -> do
    let Dims nr1 nc1 = Grid.dims input
    let Dims nr2 nc2 = Grid.dims output
    Rect (Index i1 j1) (Dims dx1 dy1) <- liftO $ Grid.nonBlankRect input
    Rect (Index i2 j2) (Dims dx2 dy2) <- liftO $ Grid.nonBlankRect output
    pure $ (top && (i1 == i2),
            bottom && (nr1 - (i1 + dx1) == nr2 - (i2 + dx2)),
            left && (j1 == j2),
            right && (nc1 - (j1 + dy1) == nc2 - (j2 + dy2)))

  guard $ any id [top, bottom, left, right] -- doesn't yet guard that some values are non-zero
  newInputs  <- Ex.mapM (cropOn crops) inputs
  newOutputs <- mapM (cropOn crops) outputs
  guard $ newInputs  /= inputs -- note: this guards that some of the values are non-zero
  guard $ newOutputs /= outputs

  crops <- oneOf "focusIO" [(show crops, crops)]
  let reconstruct guesses = MaybeT . pure $ mapM (uncurry $ uncropOn crops) (zip (Ex.test inputs) guesses)
  pure $ TacticResult.Decompose (Goal newInputs newOutputs ctx) reconstruct

  where
    cropOn :: (Bool, Bool, Bool, Bool) -> Grid Color -> SolveM (Grid Color)
    cropOn crops@(top, bottom, left, right) g = do
      let Dims nr nc  = Grid.dims g
      Rect (Index i j) (Dims dx dy) <- liftO $ Grid.nonBlankRect g
      let Index ulr ulc    = Index (if top then i else 0) (if left then j else 0)
      let Index brr brc    = Index (if bottom then i + dx else nr) (if right then j + dy else nc)
      let newRect = Rect (Index ulr ulc) (Dims (brr - ulr) (brc - ulc))
      pure $ Grid.getRect g newRect

    uncropOn :: (Bool, Bool, Bool, Bool) -> Grid Color -> Grid Color -> Maybe (Grid Color)
    uncropOn (top, bottom, left, right) input guess = do
      let Dims nr nc = Grid.dims input
      Rect (Index i j) (Dims dx dy) <- Grid.nonBlankRect input

      let nTop    = if top    then i             else 0
      let nBottom = if bottom then nr - (i + dx) else 0
      let nLeft   = if left   then j             else 0
      let nRight  = if right  then nc - (j + dy) else 0

      let Dims gr gc = Grid.dims guess
      let newRows    = gr + nTop  + nBottom
      let newCols    = gc + nLeft + nRight
      Grid.embedRectInBlank (Dims newRows newCols) (Rect (Index nTop nLeft) (Dims gr gc)) guess
