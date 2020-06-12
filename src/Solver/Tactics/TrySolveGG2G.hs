-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.TrySolveGG2G where

import Debug.Trace
import Data.List
import qualified Util.List as List
import Util.Imports
import Solver.SolveM
import Solver.Goal
import Lib.Axis
import Lib.Corner
import Lib.Ordering
import Lib.Blank
import Lib.Color
import Lib.Index
import Lib.Grid (Grid, PartitionSepData(..))
import Lib.Dims (Dims(Dims))
import qualified Lib.Dims as Dims
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.BGrid as Box
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Search.SearchT
import Search.DFS
import Synth1.Basic
import Lib.Features
import Data.Maybe (fromJust)
import Solver.Synth1Context


trySolveGG2G :: GoalGG2G -> SolveM TacticResult
trySolveGG2G goal = find1 "trySolveGG2G" $ choice "trySolveGG2G" [
    ("mapIf",       mapIfGG2G  goal),
    ("reduce",      reduceGG2G goal),
    ("select",      selectGG2G goal) -- really a special case of reduce
    ]

mapIfGG2G :: GoalGG2G -> SolveM TacticResult
mapIfGG2G goal@(Goal inputs outputs ctx) = do
  guard $ all (\(input, output) -> Box.dims input == Grid.dims output) (zip (Ex.train inputs) outputs)
  runSynth11 ctx $ do
    phiGroup2Bool <- enumAllGroupBoolFeatures Grid.enumColorSets
    mapFns :: Ex (Grid Color -> Color) <- enumReduceFeatures
    let guesses = Ex.map (\(mapFn, input) ->
                            -- TODO: PERF
                            let sgs = Box.toList input
                                bs  = Grid.fromList (Box.dims input) (phiGroup2Bool sgs)
                            in
                              Grid.fromFunc (Box.dims input) $ \idx ->
                              if Grid.get bs idx
                              then mapFn (Box.get input idx)
                              else blank) (Ex.zip mapFns inputs)
    guard $ all (\(guess, output) -> guess == output) (zip (Ex.train guesses) outputs)
    pure $ TacticResult.Guess $ Ex.test guesses

reduceGG2G :: GoalGG2G -> SolveM TacticResult
reduceGG2G goal@(Goal inputs outputs ctx) = do
  guard $ all (\(input, output) -> Dims.all (Box.dims input) (\idx -> Grid.sameDims (Box.get input idx) output)) (zip (Ex.train inputs) outputs)
  runSynth11 ctx $ do
    binOps :: Ex (Grid Color -> Grid Color -> Grid Color) <- enumBinOps
    -- is this gross style?
    guesses <-
      -- gross special case, but could be expanded
      if List.allSame (flip map (Ex.toBigList inputs) (\ig -> Box.dims ig)) &&
         Box.nCells ((Ex.train inputs) !! 0) < 9 -- have to check this here so we can check other branches upon failure
      then do
        -- if all ig dims are the same, and has less than 9 total cells, try all orderings
        let inDims :: Dims = Box.dims $ (Ex.train inputs) !! 0
        (transformedInputs :: Ex (Box.Grid (Grid Color))) <- do
          -- if we have even fewer subgrids (< 5), try some more magic -- transform the grids
              if (Dims.nIdxs inDims) < 5 then do
                (phis :: [Grid Color -> Grid Color]) <- flip mapM (Dims.allIdxs inDims) (\_ -> Grid.enumGridPreserving)
                pure $ flip Ex.map inputs (\input -> flip Box.map input (\idx val ->
                         let transformer = phis !! (Dims.index2int inDims idx) in
                           transformer val))
              -- otherwise don't transform
              else pure inputs
        permutation <- enumListElems (Data.List.permutations (Dims.allIdxs inDims))
        pure $ Ex.map (\(input, binOp) ->
          Box.reduceBinOp binOp input permutation) (Ex.zip transformedInputs binOps)
      else do
          (ax :: Axis) <- oneOf "enumOrthoAxis" [("horizontal", Horizontal), ("vertical", Vertical)]
          (corn :: Corner) <- enumVals
          (cyc :: Cycle) <- enumVals
          let orderingFn :: Dims -> Maybe [Index] = getOrdering ax corn cyc
          pure $ Ex.map (\(input, binOp) -> Box.reduceBinOp binOp input (fromJust (orderingFn (Box.dims input)))) (Ex.zip inputs binOps)
    guard $ all (\(guess, output) -> guess == output) (zip (Ex.train guesses) outputs)
    pure $ TacticResult.Guess (Ex.test guesses)

selectGG2G :: GoalGG2G -> SolveM TacticResult
selectGG2G goal@(Goal inputs outputs ctx) = do
  -- Note the guard is *any*, since we will be selecting a special one
  guard $ all (\(input, output) -> Dims.any (Box.dims input) (\idx -> Grid.sameDims (Box.get input idx) output)) (zip (Ex.train inputs) outputs)
  phiGroup2Bool <- enumAllGroupBoolFeatures Grid.enumColorSets
  -- TODO: Grid.toList is unnecessarily slow
  let specials = map fst . filter snd . (\gs -> zip gs (phiGroup2Bool gs)) . Box.toList
  flip Ex.mapM inputs $ \input -> guard $ (length . specials $ input) == 1
  for_ (zip (Ex.train inputs) outputs) $ \(input, output) -> guard $ (head . specials $ input) == output
  let guesses = map (head . specials) (Ex.test inputs)
  pure $ TacticResult.Guess guesses

splitGG2G :: GoalGG2G -> SolveM TacticResult
splitGG2G goal@(Goal inputs outputs ctx) = do
  guard $ all (\(input, output) -> Box.dims input == Grid.dims output) (zip (Ex.train inputs) outputs)
  guard $ all ((>1) . Box.nCells) inputs
  let newInputs    :: Ex (Grid Color)       = Ex (concatMap Box.toList (Ex.train inputs)) (concatMap Box.toList (Ex.test inputs))
  let newOutputs   :: ForTrain (Grid Color) = concatMap (map (Grid.const $ Dims 1 1) . Grid.toList) outputs
  let newCtxInts   :: [Choice (Ex Int)]     = flip map (ctxInts ctx) $ \(name, ints :: Ex Int) ->
        (name, Ex (flattenCore (Ex.train inputs) (Ex.train ints)) (flattenCore (Ex.test inputs) (Ex.test ints)))
  let newCtxColors :: [Choice (Ex Color)]   = flip map (ctxColors ctx) $ \(name, colors :: Ex Color) ->
        (name, Ex (flattenCore (Ex.train inputs) (Ex.train colors)) (flattenCore (Ex.test inputs) (Ex.test colors)))
  let newCtx       :: Synth1Context         = (emptySynth1Context (length (Ex.train newInputs)) (length (Ex.test newInputs))) {
        ctxInts = newCtxInts,
        ctxColors = newCtxColors
        }
  pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) (MaybeT . pure . reconstruct (Ex.test inputs))
    where
    flattenCore xss feature = flip concatMap (zip (map length xss) feature) $ \(k, f) -> replicate k f

    reconstruct []             []      = pure []
    reconstruct (input:inputs) guesses = do
      let dims = Box.dims input
      guard $ length guesses >= Dims.nCells dims
      nextGuess :: Grid Color <- Grid.unpartitionEven $ Box.fromList dims $ take (Dims.nCells dims) guesses
      rest <- reconstruct inputs $ drop (Dims.nCells dims) guesses
      pure $ nextGuess : rest
