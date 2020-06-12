-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Permutation where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
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
import Search.SearchT
import Lib.Blank
import qualified Lib.Parse as Parse
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Solver.Parse
import Solver.Tactics.GuessDims
import qualified Synth.Spec as Spec
import Search.DFS
import Synth.Basic
import Synth1.Basic
import Synth.Sequence
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Spec.DSpec (DSpec(DSpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.Spec.DSpec as DSpec

permutation :: StdGoal -> SolveM TacticResult
permutation goal@(Goal inputs outputs ctx) = find1 "permutation" $ do
  -- TODO: make sure alignAxes will ensure this property
  guard $ all ((==1) . Grid.nCols) outputs || all ((==1) . Grid.nRows) outputs
  guard $ any ((>1)  . Grid.nCols) outputs || any ((>1)  . Grid.nRows) outputs
  guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) -> Set.isSubsetOf (Grid.distinctVals nonBlank output) (Grid.distinctVals nonBlank input)

  ParseResult inShapes _ <- enumUniqueParses goal [
    Parse.Options   { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksByColor },
    Parse.Options   { Parse.kind = Parse.ParseGlobal,     Parse.color = Parse.ParseNoBlanksByColor }
    ]

  shapes2bools :: [Shape Color] -> [Bool] <- enumAllGroupBoolFeatures Shape.enumSetFeatures
  for_ (zip (Ex.train inShapes) outputs) $ \(inShapes, output) ->
    for_ (zip inShapes $ shapes2bools inShapes) $ \(inShape, keep) -> do
      c <- liftO $ Shape.uniformColorOpt inShape
      guard $ keep == Set.member c (Grid.distinctVals nonBlank output)

  let keptInShapes :: Ex [Shape Color] = flip Ex.map inShapes $ \(inShapes :: [Shape Color]) ->
        map fst . filter snd $ zip inShapes (shapes2bools inShapes)

  for_ (zip (Ex.train keptInShapes) outputs) $ \(keptInShapes, output) -> do
    guard $ length keptInShapes == Dims.nCells (Grid.dims output)

  for_ (Ex.test keptInShapes) $ \keptInShapes -> do
    guard $ length keptInShapes > 1

  -- TODO: could filter non-permutations here
  let positionLabels :: ForTrain [[Int]] = flip map (zip (Ex.train keptInShapes) outputs) $ \(inShapes :: [Shape Color], output :: Grid Color) ->
        List.cartesianProduct $ flip map inShapes $ \inShape ->
          flip filter (List.range (length inShapes)) $ \i ->
            Shape.uniformColorOpt inShape == Just (Grid.get output (Dims.int2index (Grid.dims output) i))

  -- TODO: could filter non-permutations here
  inputFeatures :: Ex [Int] <- do
    shape2ints :: Shape Color -> Int <- enumIntFeatures
    neg :: Int -> Int <- oneOf "negate" [("no", id), ("yes", \k -> -k)]
    pure $ Ex.map (map (neg . shape2ints)) keptInShapes

  let dspec :: DSpec (Ex [Int]) [Int] = DSpec (Ex.getInfo inputs) inputFeatures positionLabels
  espec :: ESpec (Ex [Int]) [Int] <- DSpec.blast dspec

  testPositions <- find1E "synthPermutation" $ synthPermutation espec

  let sortedColors :: ForTest [Color] = flip map (zip (Ex.test keptInShapes) testPositions) $ \(inShapes, positions) ->
        map (Maybe.fromJust . Shape.uniformColorOpt . fst) . sortOn snd $ (zip inShapes positions)

  let fat :: Bool = Dims.isFat (Grid.dims $ head outputs)
  let guesses :: ForTest (Grid Color) = flip map sortedColors $ \sortedColors ->
        Grid.fromList (if fat then Dims 1 (length sortedColors) else Dims (length sortedColors) 1) sortedColors

  pure $ TacticResult.Guess guesses
