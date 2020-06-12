-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Denoise where

import Util.Imports
import Data.Function
import qualified Util.List as List
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Rect as Rect
import Lib.Axis
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Solver.TacticResult (TacticResult(Decompose))
import qualified Solver.TacticResult as TacticResult
import Lib.Color
import Lib.Blank
import Synth1.Basic
import Solver.Synth1Context (Synth1Context(ctxColors))
import qualified Data.List as List
import qualified Lib.Shape as Shape
import Lib.Shape (Shape(Shape))
import qualified Lib.Parse as Parse
import Solver.Parse
import qualified Data.Map as Map
import Debug.Trace

{-
  `denoise` parses ortho shapes by color, and discards an isolated color

  'isolated' means that color has a lot of shapes such that most of the shapes are small
  we also ensure that isolated colors do not persist between training inputs and outputs
  if input and output have same dims

   Currently, we ensure that we discard a color if it is the only isolated color.
-}

data DenoiseOpts = DenoiseOpts {
  avgThreshold       :: Float,    -- average shape size must be smaller than this
  nSmallThreshold    :: Int,      -- there must be at least this many shapes of the color
  nIsolatedThreshold :: Maybe Int -- if Just k, then there can be at most k candidate colors
  }

defaultDenoiseOpts = DenoiseOpts 3.0 5 (Just 1)

denoise :: StdGoal -> SolveM TacticResult
denoise goal@(Goal inputs outputs ctx) = do
  guard $ flip Ex.all inputs $ \input -> Set.size (Grid.distinctVals nonBlank input) > 1

  let parseOpts = Parse.Options { Parse.kind = Parse.ParseLocalAny, Parse.color = Parse.ParseNoBlanksByColor }
  guard $ Parse.color parseOpts == Parse.ParseNoBlanksByColor -- invariant: shapes are monochromatic!
  ParseResult pInputs pOutputs <- getParseResult parseOpts goal

  (isolatedColors, newInputs) :: (Ex [Color], Ex (Grid Color)) <- fmap Ex.unzip $ flip Ex.mapM (Ex.zip inputs pInputs) $ \(input, shapes) -> denoiseGrid input shapes

  for_ (zip3 (Ex.train inputs) outputs (Ex.train isolatedColors)) $ \(input, output, cs) ->
    when (Grid.sameDims input output) $
      guard $ Dims.all (Grid.dims input) $ \idx -> (Grid.get input idx `elem` cs) <= (Grid.get output idx /= Grid.get input idx)

  let newCtx = if Ex.all (\cs -> length cs == 1) isolatedColors
               then ctx {ctxColors = ctxColors ctx ++ [("denoise", Ex.map head isolatedColors)] }
               else ctx
  -- liftIO . traceIO $ show (head . Ex.train $ newInputs)
  pure $ Decompose (Goal newInputs outputs newCtx) pure

denoiseGrid :: Grid Color -> [Shape Color] -> SolveM ([Color], Grid Color)
denoiseGrid input shapes = do
  isolatedColors <- computeIsolatedColors input shapes defaultDenoiseOpts
  pure . (isolatedColors,) $ flip Grid.map input $ \idx c -> if c `elem` isolatedColors then blank else c

computeIsolatedColors :: Grid Color -> [Shape Color] -> DenoiseOpts -> SolveM [Color]
computeIsolatedColors input shapes (DenoiseOpts avgThreshold nSmallThreshold nIsolatedThreshold) = do
  let groupedShapes = List.groupBy ((==) `on` Shape.firstVal) . List.sortBy (comparing Shape.firstVal) $ shapes

  let isolatedColors :: [Color] = map (Maybe.fromJust . Shape.firstVal . head) $ flip filter groupedShapes $ \shapes ->
        let sizes   = map Shape.nPoints shapes
            avg     = List.avg sizes
            nSmalls = length . filter (\size -> fromIntegral size < avgThreshold) $ sizes
        in
          avg < avgThreshold && nSmalls >= nSmallThreshold

  guard . not . null $ isolatedColors

  case nIsolatedThreshold of
    Nothing -> pure ()
    Just thresh -> guard $ length isolatedColors <= thresh

  pure isolatedColors
