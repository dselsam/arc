-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
module Solver.Tactics.Split where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import Lib.Blank
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
import qualified Lib.Parse as Parse
import qualified Lib.AlignShapes as AlignShapes
import Solver.Parse (getParseResult, enumUniqueParses, enumUniqueAlignments, ParseResult(ParseResult))
import Synth1.Basic
import Solver.Synth1Context
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
import Lib.Shape (Shape(Shape))
import qualified Lib.Shape as Shape
import qualified Lib.Rect as Rect

split :: StdGoal -> SolveM TacticResult
split goal@(Goal inputs outputs ctx) = find1 "split" $ do
  guard $ all (uncurry Grid.sameDims) $ zip (Ex.train inputs) outputs

  ParseResult inShapes outShapes <- enumUniqueParses goal [
      Parse.Options { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksAny }
      , Parse.Options   { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }

      ]

  guard $ all (not . null) inShapes
  guard $ any ((>1) . length) inShapes
  guard $ all ((<=4) . length) inShapes

  outShapes :: ForTrain [Maybe (Shape Color)] <- enumUniqueAlignments (Ex.train inShapes) outShapes [
    AlignShapes.RevAlignPoint2Shape 100
    ]

  outShapes :: ForTrain [Shape Color] <- mapM (liftO . mapM id) outShapes

  guard $ flip any [Shape.subsetMatches, flip Shape.subsetMatches, Shape.sameIndices] $ \phi ->
    flip all (zip (Ex.train inShapes) outShapes)$ \(inShapes, outShapes) -> all (uncurry phi) (zip inShapes outShapes)

  guard $ flip all (zip outputs outShapes) $ \(output, outShapes) -> flip all outShapes $ \outShape -> Rect.dims (Shape.enclosingRect outShape) /= Grid.dims output

  let rectDeltas :: ForTrain [Rect] = flip map (zip (Ex.train inShapes) outShapes) $ \(inShapes, outShapes) ->
        flip map (zip inShapes outShapes) $ \(inShape, outShape) -> Shape.enclosingRect outShape - Shape.enclosingRect inShape

  let (flatInShapes, unflatten) = Ex.flatten inShapes
  let flatRectDeltas = concat rectDeltas
  intFeatures <- lift . precompute $ do
        rect2int <- enumIntFeatures
        pure $ Ex.map rect2int flatInShapes

  -- Could be a synth call but we keep it simple
  guard $ all (all (== (Rect (Index 0 0) (Dims 0 0)))) rectDeltas
  let guessRectDeltas :: Ex [Rect] = Ex.map (map $ \_ -> Rect (Index 0 0) (Dims 0 0)) inShapes
  --guessRectDeltas :: Ex [Rect] <- fmap unflatten $ find1 "rectDeltas" . synthInts2Rect $ ESpec (Ex.getInfo flatInShapes) (EagerFeatures intFeatures) flatRectDeltas

  -- unnormalized rectangles
  let rects :: Ex [Rect] = flip Ex.map (Ex.zip inShapes guessRectDeltas) $ \(inShapes, rDeltas) ->
        flip map (zip inShapes rDeltas) $ \(inShape, rDelta) -> Shape.enclosingRect inShape + rDelta

  let newInputsSeq :: Ex [Grid Color] = flip Ex.map (Ex.zip3 inputs inShapes rects) $ \(input, inShapes, rects) ->
        flip map (zip inShapes rects) $ \(inShape, rect) ->
          let Rect idx dims = rect in Grid.fromShapes dims [Shape.shiftIndexRev inShape idx]

  let newOutputsSeq :: ForTrain [Grid Color] = flip map (zip outShapes (Ex.train rects)) $ \(outShapes, rects) ->
        flip map (zip outShapes rects) $ \(outShape, rect) ->
          let Rect idx dims = rect in Grid.fromShapes dims [Shape.shiftIndexRev outShape idx]

  let (newInputs, unflatten) = Ex.flatten newInputsSeq
  let (newOutputs, _)        = List.flatten newOutputsSeq
  -- TODO: track the context
  let newCtx                 = emptySynth1Context (length (Ex.train newInputs)) (length (Ex.test newInputs))

  let reconstruct guesses = do
        let gridGuesses :: ForTest [Grid Color] = Ex.test $ unflatten (Ex outputs guesses)
        mapM (List.uncurry3 embedAllGrids) (zip3 (Ex.test inputs) (Ex.test rects) gridGuesses)

  pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) reconstruct

  where
    embedAllGrids input rects grids = embedAllGridsCore (Grid.const (Grid.dims input) blank) rects grids

    embedAllGridsCore g [] [] = pure g
    embedAllGridsCore g (rect:rects) (grid:grids) = do
      g1 <- MaybeT . pure $ Grid.embedRectIn g rect grid
      embedAllGridsCore g1 rects grids
