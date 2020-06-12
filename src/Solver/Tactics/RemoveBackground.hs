-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.RemoveBackground where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import Synth1.Arith
import Search.DFS
import Lib.Features
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)

---------------
-- Remove Background
---------------
-- Requires:
--   - FIXME
-- Considers:
--   - FIXME

removeBackground :: StdGoal -> SolveM TacticResult
removeBackground goal =
  choice "removeBackground" [
    ("input", removeBackgroundInputs goal),
    ("IO",    removeBackgroundIO goal)
    ]


removeBackgroundCore :: Grid Color -> Maybe Color
removeBackgroundCore g = do
  let (cs, maxVal) = Grid.majorityNonBlankVals g
  guard $ (not (null cs)) && (length cs) == 1
  let maxValPair :: (Color, Int) = (head cs, maxVal)
  guard $ maxVal > ((Grid.nRows g) * (Grid.nCols g)) `div` 2
  -- FIXME: Guard that enclosing rectangle of color shape is size of whole grid
  pure $ fst maxValPair

removeBackgroundInputs :: StdGoal -> SolveM TacticResult
removeBackgroundInputs (Goal inputs outputs ctx) = find1 "removeBackgroundInputs" $ do
  (inputBgColors :: Ex Color) <- liftO $ flip Ex.mapM inputs $ removeBackgroundCore
    -- FIXME: Guard that the color isn't the max color of the output (less strict than saying it can't appear in the output at all)
  guard $ flip all (zip outputs (Ex.train inputBgColors)) $ \(og, inputBg) ->
    not . Int.any (Grid.nRows og * Grid.nCols og) $ \i ->
      (Grid.getG og (Dims.int2index (Grid.dims og) i)) == inputBg
  let newInputs :: Ex (Grid Color) = flip Ex.map (Ex.zip inputs inputBgColors) $ \ (ig, c) ->
        Grid.swapVals ig c blank
  pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure

removeBackgroundIO :: StdGoal -> SolveM TacticResult
removeBackgroundIO (Goal inputs outputs ctx) = find1 "removeBackgroundIO" $ do
  (inputBgColors :: Ex Color) <- liftO $ flip Ex.mapM inputs $ removeBackgroundCore
  (outputBgColors :: ForTrain Color) <- liftO $ flip mapM outputs $ removeBackgroundCore

  guard $ flip all (zip outputBgColors (Ex.train inputBgColors)) $ \(c1, c2) -> c1 == c2
  let newInputs :: Ex (Grid Color) = flip Ex.map (Ex.zip inputs inputBgColors) $ \ (ig, c) ->
        Grid.swapVals ig c blank
  let newOutputs :: ForTrain (Grid Color) = flip map (zip outputs outputBgColors) $ \ (og, c) ->
        Grid.swapVals og c blank
  let reconstruct guesses = flip mapM (zip guesses (Ex.test inputBgColors)) $ \(guess, outputC) -> do
        pure $ Grid.swapVals guess blank outputC
  pure $ TacticResult.Decompose (Goal newInputs newOutputs ctx) reconstruct
