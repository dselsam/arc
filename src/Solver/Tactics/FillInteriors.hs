-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.FillInteriors where

import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import qualified Data.Maybe as Maybe
import qualified Solver.Goal
import Search.SearchT
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Index as Index
import qualified Lib.Rect as Rect
import qualified Data.Map as Map
import qualified Util.Map as Map
import Lib.Axis
import Lib.Index (Index(Index))
import Search.Guess (Guess(Guess))
import qualified Search.Guess as Guess
import Search.History (History)
import qualified Search.History as History
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color
import Lib.Blank
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import qualified Lib.Parse as Parse
import qualified Lib.AlignShapes as AlignShapes
import Solver.Parse (getParseResult, ParseResult(ParseResult))
import Synth1.Basic
import Solver.Goal
import Solver.Synth1Context (ctxHaveFocused)
import Synth.Int2Bool
import Synth.Bool
import Synth.Core
import Synth.EagerFeatures
import Synth.LazyFeatures
import Synth.Sequence
import Search.DFS
import Synth.Spec
import qualified Synth.Spec as Spec
import qualified Lib.Shape as Shape
import qualified Solver.Tactics.Blast.Goal as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import Solver.Tactics.Blast.Mask (Mask(Mask))
import qualified Solver.Tactics.Blast.Mask as Mask
import Solver.Tactics.Blast.Candidate (Candidate(Candidate))
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Solver.Tactics.DyeInputs (synthG2C)
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Lib.Features

fillInteriors :: Solver.Goal.StdGoal -> SolveM TacticResult
fillInteriors goal@(Solver.Goal.Goal inputs outputs ctx) = do
  guard $ not (ctxHaveFocused ctx)
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  ParseResult inShapes _         <- flip getParseResult goal $ Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseOnlyBlanks }
  ParseResult _        outShapes <- flip getParseResult goal $ Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }

  -- Note: the shapes are *unnormalized*
  -- TODO: make them units? it currently clashes with the synth1 instances so being expedient and keeping them colors
  shape2colors :: ForTrain (Map (Shape Color) (Maybe Color)) <- flip mapM (zip (Ex.train inShapes) outShapes) $ \(inShapes, outShapes) ->
    List.iterM inShapes Map.empty $ \acc inShape -> do
      case filter (\outShape -> Shape.sameIndices inShape outShape) outShapes of
        [] -> pure $ Map.insert inShape Nothing acc
        [outShape] -> do
          c <- liftO $ Shape.uniformColorOpt outShape
          pure $ Map.insert inShape (Just c) acc
  guard $ any (any Maybe.isJust . Map.elems) shape2colors
  let labels :: ForTrain [Maybe Color] = flip map (zip (Ex.train inShapes) shape2colors) $ \(inShapes, s2c) -> map (s2c Map.!) inShapes

  -- TODO: could be much more sophisticated
  -- TODO: pre-filter the unbounded shapes, so we compute features only on the interiors
  boundedFeaturesSeq :: [Choice (Ex [Bool])] <- lift . precompute $ do
    LazyFeatures.choose $ Shape.getBoundedLazyFeatures (Ex.map Grid.dims inputs) inShapes

  boolFeaturesSeq :: [Choice (Ex [Bool])] <- lift . precompute $ do
    shapes2bools :: [Shape Color] -> [Bool] <- enumAllGroupBoolFeatures (deadend "shapes are blank" :: SolveM (Shape Color -> Set ()))
    pure $ Ex.map shapes2bools inShapes

  intFeaturesSeq :: [Choice (Ex [Int])] <- lift . precompute $ do
    shape2int :: Shape Color -> Int <- enumIntFeatures
    pure $ Ex.map (map shape2int) inShapes

  let (inShapesFlat   :: Ex (Shape Color), reconstructFlattened) = Ex.flatten inShapes
  let boolFeatures    :: [Choice (Ex Bool)]     = flip map (boundedFeaturesSeq ++ boolFeaturesSeq) $ \(name, bs) -> (name, fst $ Ex.flatten bs)
  let intFeatures     :: [Choice (Ex Int)]      = flip map intFeaturesSeq                          $ \(name, ks) -> (name, fst $ Ex.flatten ks)
  let labelsFlat      :: ForTrain (Maybe Color) = concat labels

  -- TODO: how can we make use of the ints?? Still navigating the new synth design. For now they may as well be units.
  let spec :: ESpec (EagerFeatures Bool, EagerFeatures Int) (Maybe Color) = ESpec (Ex.getInfo inShapesFlat) (EagerFeatures boolFeatures, EagerFeatures intFeatures) labelsFlat

  guessesFlat :: Ex (Maybe Color) <- find1 "fillInteriors" $ decisionListID [1, 2, 3, 4] constValueE spec
  let guesses :: Ex [Maybe Color] = reconstructFlattened guessesFlat

  let newInputs :: Ex (Grid Color) = flip Ex.map (Ex.zip3 inputs inShapes guesses) $ \(input, inShapes, guesses) ->
        let (updateInShapes, updateColors) = unzip . map (\(s, Just c) -> (s, c)) . filter (Maybe.isJust . snd) $ zip inShapes guesses in
          Grid.replacingShapes input updateInShapes (map (uncurry Shape.fill) (zip updateColors updateInShapes))

  pure $ TacticResult.Decompose (goal { inputs = newInputs }) pure
