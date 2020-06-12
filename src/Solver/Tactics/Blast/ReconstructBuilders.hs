-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.ReconstructBuilders where

import qualified Data.Maybe as Maybe
import Debug.Trace
import Util.Imports
import Util.List as List
import Data.List hiding (partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex

import Lib.Blank
import qualified Lib.Grid as Grid

import qualified Lib.Axis as Axis
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Dims as Dims
import Lib.Rect

-- FIXME: Remove unnecessary imports


-- FIXME: Don't actually have to use Maybe for any of these -- could just return the unmodified original
eqForValReconstruct :: Ex (Grid Color) -> ForTrain (Grid Color) -> Ex (Grid (Maybe Color)) -> Maybe (Ex (Grid (Maybe Color)))
eqForValReconstruct inputs outputs currentReconstructs = do
  -- shrink search size of colors
  let distinctVals :: Set Color = Grid.distinctValsInGrids (\_ -> True) $ (Ex.toBigList inputs) ++ outputs
  pure $ List.iter (Set.toList distinctVals) currentReconstructs (\reconstructs val ->
    -- intuition: if you are val in the input, you are val in the output (and this holds true
    -- for all (ig, og)
    if flip Ex.all inputs (\input -> Dims.any (Grid.dims input) $ \idx -> Grid.get input idx == val) &&
      flip all (zip (Ex.train inputs) outputs) (\(ig, og) -> Grid.subsetForVal ig og val)
    then pure $ flip Ex.map (Ex.zip reconstructs inputs) $ \(reconstruct, ig) ->
      flip Grid.map reconstruct $ \idx rVal -> if (Grid.get ig idx) == val then Just val else rVal
    else pure reconstructs)


nonBlankShapeReconstruct :: Ex (Grid Color) -> ForTrain (Grid Color) -> Ex (Grid (Maybe Color)) -> Maybe (Ex (Grid (Maybe Color)))
nonBlankShapeReconstruct inputs outputs currentReconstructs = do
  nonBlankShapes :: Ex Rect <- flip Ex.mapM inputs Grid.nonBlankRect
  -- The main guard
  guard $ flip all (zip3 (Ex.train inputs) outputs (Ex.train nonBlankShapes)) (\(ig, og, r) ->
    Dims.all (Grid.dims ig) $ \idx -> if Lib.Rect.containsIndex r idx then True
                                      else (Grid.get ig idx) == (Grid.get og idx))
  pure $ flip Ex.map (Ex.zip3 inputs currentReconstructs nonBlankShapes) $ \(ig, currReconstruct, r) ->
    flip Grid.map ig (\idx x -> if not (Lib.Rect.containsIndex r idx)
                       then Just (Grid.get ig idx)
                       else Grid.get currReconstruct idx)

-- FIXME: Don't actually have to use Maybe for any of these -- could just return the unmodified original
subsetReconstruct :: Ex (Grid Color) -> ForTrain (Grid Color) -> Ex (Grid (Maybe Color)) -> Maybe (Ex (Grid (Maybe Color)))
subsetReconstruct inputs outputs currentReconstructs =
  if all (\(ig, og) -> Grid.subset ig og) (zip (Ex.train inputs) outputs)
  then pure $ flip Ex.map (Ex.zip currentReconstructs inputs) $ \(reconstruct, ig) ->
    flip Grid.map ig $ \idx val -> if nonBlank val then Just val else (Grid.get reconstruct idx)
  else Nothing


initialReconstructs :: Ex (Grid Color) -> ForTrain (Grid Color) -> Ex (Grid (Maybe Color))
initialReconstructs inputs outputs =
  List.iter [subsetReconstruct, nonBlankShapeReconstruct, eqForValReconstruct] initial $ \rBuilder f ->
  -- uncomment if we want to rely on FocusIO
  -- List.iter [subsetReconstruct, eqForValReconstruct] initial $ \rBuilder f ->
    case f inputs outputs rBuilder of
      Just r -> pure r
      Nothing -> pure rBuilder
  where
    initial = flip Ex.map inputs $ \input -> Grid.const (Grid.dims input) Nothing
