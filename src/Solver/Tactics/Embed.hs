-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
module Solver.Tactics.Embed where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
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
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.EagerFeatures
import Search.SearchT
import Search.DFS
import Synth.Spec.ESpec (ESpec(ESpec))
import Lib.Rect (Rect(Rect))
import Solver.TacticResult
import Solver.Tactics.GuessDims
import Solver.Tactics.ExactSubgrid
import Lib.Synth
import Lib.Corner
import Lib.HasElems

expectedIdx :: Corner -> (Dims -> Dims -> Index)
expectedIdx corn =
  case corn of
    TopLeft -> \inDims outDims -> Index 0 0
    TopRight -> \inDims outDims -> (cornerIdx outDims TopRight) - (Index 0 ((Dims.nCols inDims) - 1))
    BottomLeft -> \inDims outDims -> (cornerIdx outDims BottomLeft) - (Index ((Dims.nRows inDims) - 1) 0)
    BottomRight -> \inDims outDims -> (cornerIdx outDims BottomRight) - (Index ((Dims.nRows inDims) - 1) ((Dims.nCols inDims) - 1))

checkCorner :: StdGoal -> ForTrain [Index] -> Corner -> Bool
checkCorner goal@(Goal inputs outputs ctx) matchingIdxs corn =
  flip all (zip3 (Ex.train inputs) outputs matchingIdxs) $ \(ig, og, idxs) ->
    any (== (cornerGetter (Grid.dims ig) (Grid.dims og))) idxs
  where
    cornerGetter = expectedIdx corn

getCornerIdxs :: StdGoal -> ForTest Dims -> Corner -> Ex Index
getCornerIdxs goal@(Goal inputs outputs ctx) testDims corn =
 Ex trainIdxs testIdxs
 where
   cornerGetter = expectedIdx corn
   trainIdxs = flip map (zip (Ex.train inputs) outputs) $ \(ig, og) -> cornerGetter (Grid.dims ig) (Grid.dims og)
   testIdxs = flip map (zip (Ex.test inputs) testDims) $ \(ig, outDims) -> cornerGetter (Grid.dims ig) outDims

getNewInputs :: StdGoal -> ForTest Dims -> Ex Index -> Maybe (Ex (Grid Color))
getNewInputs goal@(Goal inputs outputs ctx) testDims indexGuesses =
  flip Ex.mapM (Ex.zip3 inputs (Ex (map Grid.dims outputs) testDims) indexGuesses) $ \(input, outDims, upperLeft) ->
    Grid.embedRectInBlank outDims (Rect upperLeft (Grid.dims input)) input



embed :: StdGoal -> SolveM TacticResult
embed goal@(Goal inputs outputs ctx) = do
  for_ (zip (Ex.train inputs) outputs) $ \(input, output) -> do
    guard $ Grid.nRows input <= Grid.nRows output
    guard $ Grid.nCols input <= Grid.nCols output

  guard $ flip any (zip (Ex.train inputs) outputs) $ \(input, output) ->
    Grid.nRows input < Grid.nRows output || Grid.nCols input < Grid.nCols output

  testDims <- synthDims goal

  let matchingIdxs :: ForTrain [Index] = flip map (zip (Ex.train inputs) outputs) $ \(ig, og) ->
        Grid.findSubgrids og (Grid.dims ig) (== ig)

  -- guard that we have at least one match for each
  guard $ Prelude.all (\idxs -> not (null idxs)) matchingIdxs

  let allCandidates :: [[Index]] = sequence matchingIdxs

  -- check that we don't have too many matches
  -- is < 25 too strict?
  if (length allCandidates) < 25 then
    runSynth11 ctx $ do
      (candidates :: ForTrain Index) <- liftL $ allCandidates
      intFeatures  :: [Choice (Ex Int)] <- lift . precompute . LazyFeatures.choose . getBasicLazyFeatures $ Ex.map Grid.dims inputs
      indexGuesses :: Ex Index <- synthInts2Index $ ESpec (Ex.getInfo inputs) (EagerFeatures intFeatures) candidates
      newInputs :: Ex (Grid Color) <- liftO $ getNewInputs goal testDims indexGuesses

      pure $ Decompose (Goal newInputs outputs ctx) pure

  else do
    matchingCorn <- liftO $ flip List.first elems (\corn ->
      if checkCorner goal matchingIdxs corn then Just corn else Nothing)
    let idxGuesses :: Ex Index = getCornerIdxs goal testDims matchingCorn
    newInputs :: Ex (Grid Color) <- liftO $ getNewInputs goal testDims idxGuesses
    pure $ Decompose (Goal newInputs outputs ctx) pure
