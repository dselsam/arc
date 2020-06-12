-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.TrySolveGG2GG where

import Solver.Synth1Context
import Debug.Trace
import Data.List (zip4, nub, length, sortOn)
import Util.Imports
import qualified Data.List as List
import qualified Util.List as List
import Solver.SolveM
import qualified Data.Map as Map
import Solver.Goal
import Synth.ExInfo (ExInfo(ExInfo))
import Synth1.Basic
import qualified Lib.BGrid as Box
import Lib.Color (Color)
import Lib.Blank
import Lib.Index
import Lib.Dims (Dims(Dims))
import Lib.Grid (Grid, PartitionSepData(..))
import qualified Lib.Dims as Dims
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult, Reconstruct)
import qualified Solver.TacticResult as TacticResult
import Search.SearchT
import Lib.Features
import Lib.Axis (Axis(..))
import Lib.Corner (Corner)
import Lib.Ordering
import Data.Maybe (fromJust)
import Lib.Symmetry
import qualified Lib.Symmetry as Symmetry

trySolveGG2GG :: GoalGG2GG -> SolveM (ForTest (Box.Grid (Grid Color)))
trySolveGG2GG goal = choice "trySolveGG2GG" [
  ("specialMapBin",       specialMapBinGG2GG goal),
  ("specialMapAtIndices", specialMapAtIndices goal),
  ("sorter", sortSubgridsGG2GG goal)
  --("symmetries", symmetryGG2GG goal)
  ]

symmetryGG2GG :: GoalGG2GG -> SolveM (ForTest (Box.Grid (Grid Color)))
symmetryGG2GG goal@(Goal inputs outputs ctx) = do
  -- TODO: any guards we can add here?
  runSynth11 ctx $ do
    ax <- enumVals

    -- note that we don't support union here
    let f input = Box.reflectAround input ax

    for_ (zip (Ex.train inputs) outputs) $ \(ig, og) -> do
             let guess = f ig
             guard $ guess == og

    let guesses = map f (Ex.test inputs)
    pure guesses


sortSubgridsGG2GG goal@(Goal inputs outputs ctx) = do
  -- guard that inputs and outputs are split the same way
  guard $ all (uncurry Grid.allSameDims) (zip (Ex.train inputs) outputs)
  -- guard that it's an even split
  guard $ Ex.all (\input -> Dims.allSame (Box.dims input) $ \idx -> Grid.dims (Box.get input idx)) inputs
  runSynth11 ctx $ do
    -- choose sorter
    (sorter :: Grid Color -> Int) <- choice "sortSubgrids.sorter" [
      ("nNonBlanks", pure $ Grid.nNonBlanks),
      ("nBlanks", pure $ Grid.nBlanks),
      ("nDistinctVals", pure $ Grid.nDistinctVals (\_ -> True)),
      ("nNonBlankVals", pure $ Grid.nNonBlankVals),
      ("nVal", do
          (c :: Color) <- enumVals
          pure $ \g -> Grid.nVal g c)
      ]

    -- turn each input into list of index and its val (a grid color). A grid is [(index, Grid Color)]
    -- get int value at each index -- get lists of (index, int). However, we really want [(index, Grid Color, int)]
    let allInputInfo :: Ex [(Index, Grid Color, Int)] = flip Ex.map inputs $ \input ->
          flip map (Box.toListWithIndices input) $ \(index, g) -> (index, g, sorter g)

    -- check that values are unique
    guard $ flip Ex.all allInputInfo (\inputInfo ->
              let inputInts :: [Int] = flip map inputInfo (\(_, _, num) -> num) in
                length (nub inputInts) == length inputInts)
    -- get ordering
    let allSortedInputInfo :: Ex [(Index, Grid Color, Int)] =
          flip Ex.map allInputInfo $ \inputInfo ->
            sortOn (\(_, _, num) -> num) inputInfo
    (ax :: Axis) <- oneOf "enumOrthoAxis" [("horizontal", Horizontal), ("vertical", Vertical)]
    (corn :: Corner) <- enumVals
    (cyc :: Cycle) <- enumVals
    let orderingFn :: Dims -> Maybe [Index] = getOrdering ax corn cyc
    -- map the following: zipped (a) sorted list of (index, Grid Color, int), (b) ordering indices. Replace the index
    -- in the list of (index, int) with the ordering index
    let finalVals :: Ex [(Index, Grid Color)] = flip Ex.map (Ex.zip allSortedInputInfo inputs) $ \(sortedInfo, ig) ->
          let orderingInputIdxs :: [Index] = fromJust (orderingFn (Box.dims ig)) in
            flip Prelude.map (zip orderingInputIdxs sortedInfo) $ \(ordIdx, (_, gVal, _)) -> (ordIdx, gVal)
    -- final guard!
    -- you now have lists of tuples -- each tuple contains an index and a val. We can check soundness
    guard $ flip all (zip (Ex.train finalVals) outputs) $ \(valInfo, og) ->
      flip all valInfo $ \(idx, gVal) -> (Box.get og idx) == gVal

    let finalValMaps :: Ex (Map Index (Grid Color)) = flip Ex.map finalVals $ \idxVals -> Map.fromList idxVals
    -- If sound, pass along!
    let guesses :: Ex (Box.Grid (Grid Color)) = flip Ex.map (Ex.zip inputs finalValMaps) $ \(ig, valMap) ->
          Box.fromFunc (Box.dims ig) $ \idx -> valMap Map.! idx
    pure $ Ex.test guesses








-- TODO: pretty specialized, could generalize in a number of ways
-- Motivated by 1e32b0e9
specialMapBinGG2GG goal@(Goal inputs outputs ctx) = do
  guard $ all (uncurry Grid.allSameDims) (zip (Ex.train inputs) outputs)
  guard $ Ex.all (\input -> Dims.allSame (Box.dims input) $ \idx -> Grid.dims (Box.get input idx)) inputs
  runSynth11 ctx $ do
    phiGroup2Bool <- enumAllGroupBoolFeatures Grid.enumColorSets
    -- TODO: Grid.toList is unnecessarily slow
    let getSpecials :: Box.Grid (Grid Color) -> [Grid Color] = map fst . filter snd . (\gs -> zip gs (phiGroup2Bool gs)) . Box.toList
    flip Ex.mapM inputs $ \input -> guard $ (List.countDistinct id . getSpecials $ input) == 1
    let specials  :: Ex (Grid Color) = Ex.map (head . getSpecials) inputs
    phiGrid2Grids :: Ex (Grid Color -> Grid Color) <- enumUnaryOps
    let specialsTransformed = Ex.map (\(special, phiG2G) -> phiG2G special) (Ex.zip specials phiGrid2Grids)
    binOps :: Ex (Grid Color -> Grid Color -> Grid Color) <- enumBinOps
    let fs :: Ex (Box.Grid (Grid Color)) -> Ex (Box.Grid (Grid Color)) = \gss ->
          Ex.map (\(gs, binOp, specialTransformed) -> Box.map (\_ g -> binOp g specialTransformed) gs) (Ex.zip3 gss binOps specialsTransformed)
    let guesses = fs inputs
    guard $ all (\(guess, output) -> guess == output) (zip (Ex.train guesses) outputs)
    pure $ Ex.test guesses

-- TODO: pretty specialized, could generalize in a number of ways
-- Motivated by 6d0160f0
specialMapAtIndices :: GoalGG2GG -> SolveM (ForTest (Box.Grid (Grid Color)))
specialMapAtIndices goal@(Goal inputs outputs ctx) = do
  guard $ all (uncurry Grid.allSameDims) (zip (Ex.train inputs) outputs)
  guard $ flip Ex.all inputs $ \input -> Dims.allSame (Box.dims input) $ \idx -> Grid.dims (Box.get input idx)
  runSynth11 ctx $ do
    fs       :: Ex (Grid Color -> [Index]) <- Grid.enumMaybeIndices
    idx2idxs :: Ex (Map Index Index) <- flip Ex.mapM (Ex.zip fs inputs) $ \(f, input) -> do
      List.iterM (Box.toListWithIndices input) Map.empty $ \acc (originalIdx, g) ->
        List.iterM (f g) acc $ \acc newIdx -> do
          case Map.lookup newIdx acc of
            Nothing -> pure $ Map.insert newIdx originalIdx acc
            Just _  -> deadend "duplicate index, TODO support reductions on clashes"
    unaryFns :: Ex (Grid Color -> Grid Color) <- enumUnaryOps
    let guesses :: Ex (Box.Grid (Grid Color)) = flip Ex.map (Ex.zip3 inputs idx2idxs unaryFns) $ \(input, idx2idx, unaryFn) ->
          Box.fromFunc (Box.dims input) $ \idx2 ->
                                         case Map.lookup idx2 idx2idx of
                                           Nothing -> Grid.const (Box.dims input) blank
                                           Just idx1 -> unaryFn $ Box.get input idx1
    guard $ all (\(guess, output) -> guess == output) (zip (Ex.train guesses) outputs)
    pure $ Ex.test guesses

splitGG2GG :: Reconstruct (Box.Grid (Grid Color)) (Grid Color) -> GoalGG2GG -> SolveM TacticResult
splitGG2GG reconstructGG2G goal@(Goal pInputs pOutputs ctx) = do
  -- Motivated by cbded52d
  for_ (zip (Ex.train pInputs) pOutputs) $ \(pInput, pOutput) -> do
    guard $ Grid.allSameDims pInput pOutput
    guard $ Grid.uniformDims pInput

  let newInputs  :: Ex (Grid Color)       = Ex (concatMap splitByPosition (Ex.train pInputs)) (concatMap splitByPosition (Ex.test pInputs))
  let newOutputs :: ForTrain (Grid Color) = concatMap splitByPosition pOutputs

  let ExInfo nNewTrain nNewTest = Ex.getInfo newInputs

  -- TODO: track context
  let newCtx     :: Synth1Context         = emptySynth1Context nNewTrain nNewTest

  let reconstruct guesses = unsplitLike (Ex.test pInputs) guesses >>= reconstructGG2G
  pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) reconstruct

  where
    splitByPosition :: Box.Grid (Grid Color) -> [Grid Color]
    splitByPosition gs = do
      let outerDims :: Dims = Box.dims gs
      let innerDims :: Dims = Grid.dims (Box.get gs (Index 0 0))
      innerIdx <- Dims.allIdxs innerDims
      pure $ Grid.fromFunc outerDims $ \outerIdx -> Grid.get (Box.get gs outerIdx) innerIdx

    unsplitLike :: ForTest (Box.Grid (Grid Color)) -> ForTest (Grid Color) -> MaybeT IO (ForTest (Box.Grid (Grid Color)))
    unsplitLike []           []      = pure []
    unsplitLike (gs:pInputs) guesses = do
      let outerDims :: Dims = Box.dims gs
      let innerDims :: Dims = Grid.dims (Box.get gs (Index 0 0))
      guard $ length guesses >= Dims.nCells innerDims
      let relevantGuesses = take (Dims.nCells innerDims) guesses
      guess :: Box.Grid (Grid Color) <- Box.fromFuncM outerDims $ \oIdx ->
        Grid.fromFuncM innerDims $ \iIdx -> do
          guard $ length relevantGuesses > Dims.index2int innerDims iIdx
          let nextGuess = relevantGuesses List.!! (Dims.index2int innerDims iIdx)
          guard $ Dims.inBounds (Grid.dims nextGuess) oIdx
          pure $ Grid.get nextGuess oIdx
      rest <- unsplitLike pInputs (drop (Dims.nCells innerDims) guesses)
      pure $ guess : rest

    unsplitLike _ _ = MaybeT . pure $ Nothing
