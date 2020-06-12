-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.DyeInputs where

import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Rect as Rect
import Lib.Axis
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color
import Lib.Blank
import Synth1.Basic
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Util.List as List
import qualified Util.Map as Map
import Solver.Synth1Context (Synth1Context(..))
import Search.DFS
import Debug.Trace

{-
  `DyeInputs` will try to infer/synthesize the following data for every input:
    - `cOut : Color`
    - `keep : Map Color Bool`

  `DyeInputs` will then apply the following transformation to all inputs: every color
  will be dyed to `cOut`, unless if that color is in `keep`.
-}

dyeInputs :: StdGoal -> SolveM TacticResult
dyeInputs goal = find1 "dyeInputs" $ choice "dyeInputs" [
  ("sameDims", dyeInputsSameDims goal),
  ("diffDims", dyeInputsDiffDims goal)
  ]

dyeInputsSameDims :: StdGoal -> SolveM TacticResult
dyeInputsSameDims goal@(Goal inputs outputs ctx) = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)

  -- for input-output grids `g1` and `g2`, a color `c` is `kept`
  -- if for every `idx`, `Grid.get g1 idx == c` implies that `Grid.get g2 idx == c`
  (trainKeepMaps :: ForTrain (Map Color Bool), outputColors :: ForTrain Color) <- unzip <$> do
    flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) -> do
      let keepMap :: Map Color Bool = Dims.iter (Grid.dims input) Map.empty $ \acc idx -> pure $
            if nonBlank $ Grid.get input idx then
              Map.insertWith (&&) (Grid.get input idx) (Grid.get input idx == Grid.get output idx) acc
            else acc
      let otherOutputColors :: Set Color = Dims.iter (Grid.dims input) Set.empty $ \acc idx -> pure $
            if (nonBlank $ Grid.get output idx) && (Map.lookup (Grid.get input idx) keepMap /= Just True)
            then Set.insert (Grid.get output idx) acc
            else acc

      guard $ Set.size otherOutputColors == 1
      pure (keepMap, Set.elemAt 0 otherOutputColors)

  let trainNonKeepInputColors :: ForTrain (Set Color) = flip map trainKeepMaps $ \trainKeepMap ->
        Set.fromList (map fst . filter (not . snd) . Map.assocs $ trainKeepMap)

  guard $ flip all trainNonKeepInputColors $ not . null
  guard $ flip any (zip trainNonKeepInputColors outputColors) $ \(vs, color) ->
      (Set.size vs > 1) || (Set.size vs == 1 && (Set.elemAt 0 vs) /= color)

  testKeepMaps <- runSynth11 ctx $ synthG2KeepMaps inputs trainKeepMaps
  testColors   <- runSynth11 ctx $ synthG2C inputs outputColors

  newInputs <- flip Ex.mapM (Ex.zip3 inputs (Ex trainKeepMaps testKeepMaps) (Ex outputColors testColors)) $ \(input, keepMap, outputColor) -> pure $
    flip Grid.map input $ \idx c ->
      if isBlank c then blank else
        case Map.lookup c keepMap of
          Just True -> c
          _         -> outputColor

  let testNonKeepInputColors :: ForTest (Set Color) = flip map testKeepMaps $ \testKeepMap ->
        Set.fromList (map fst . filter (not . snd) . Map.assocs $ testKeepMap)

  let newCtx = if flip Ex.all (Ex trainNonKeepInputColors testNonKeepInputColors) $ (== 1) . Set.size
               then ctx { ctxColors = ("dyeInputs", Ex.map (Set.elemAt 0) $ Ex trainNonKeepInputColors testNonKeepInputColors):ctxColors ctx }
               else ctx

  -- @jesse: this is an assertion/sanity check right? are you sure you want silent failures for this?
  guard $ flip all (zip (Ex.train newInputs) outputs) $ \(input, output) ->
    (isJust . Grid.isUniform $ input) <= (isJust . Grid.isUniform $ output)

  pure $ TacticResult.Decompose (goal {inputs = newInputs, synthCtx = newCtx}) pure

dyeInputsDiffDims :: StdGoal -> SolveM TacticResult
dyeInputsDiffDims goal@(Goal inputs outputs ctx) = do
  guard $ not $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)

  outputColors :: ForTest Color <- flip mapM outputs $ \output -> do
    let vs :: Set Color = Grid.distinctVals nonBlank output
    guard $ Set.size vs == 1
    pure . head . Set.toList $ vs

  guard $ flip any (zip (Ex.train inputs) outputColors) $ \(input, color) ->
    let vs :: Set Color = Grid.distinctVals nonBlank input in
      (Set.size vs > 1) || (Set.size vs == 1 && (head . Set.toList $ vs) /= color)

  testColors <- runSynth11 ctx $ synthG2C inputs outputColors

  let newInputs = flip Ex.map (Ex.zip inputs (Ex outputColors testColors)) $ \(input, c) ->
        Grid.map (\_ x -> if nonBlank x then c else blank) input
  pure $ TacticResult.Decompose (goal { inputs = newInputs }) pure

synthG2C :: Ex (Grid Color) -> ForTrain Color -> Synth1M (ForTest Color)
synthG2C inputs outputs = choice "synthG2C" [
  ("groupSetValueMaps", do
      allColors :: [Color] <- enumGroupSetValueMaps Grid.enumColorSets (Ex.toBigList inputs)
      let cs = Ex.fromBigList allColors (Ex.getInfo inputs)
      guard $ Ex.train cs == outputs
      pure $ Ex.test cs),
  ("enumColor", do
      cs <- enumColorsCtx
      guard $ Ex.train cs == outputs
      pure $ Ex.test cs)
  ]

synthG2KeepMaps :: Ex (Grid Color) -> ForTrain (Map Color Bool) -> Synth1M (ForTest (Map Color Bool))
synthG2KeepMaps inputs trainKeepMaps = choice "synthG2KeepMaps" [
  ("uniformKeepMaps", replicate (length $ test inputs) <$> (liftO $ Map.glueMaps trainKeepMaps))]
