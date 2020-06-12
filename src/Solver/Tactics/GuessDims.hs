-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.GuessDims where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import Synth1.Arith
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Blank
import Lib.Color (Color(..))
import qualified Lib.Grid as Grid
import qualified Lib.Index as Index
import qualified Lib.Dims as Dims
import qualified Data.Maybe as Maybe
import qualified Lib.Rect as Rect
import qualified Synth.Ex as Ex
import Solver.Synth1Context
import Lib.Features
import Lib.Rect (Rect(..))
import Lib.Dims (Dims(..))
import Lib.Index (Index(..))
import Data.List (zip4)
import Lib.Tile (TileData(..))
import qualified Lib.Tile as Tile
import Search.DFS
import Synth1.Basic
import Lib.Synth
import qualified Solver.Synth1Context as Synth1Context
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.Spec as Spec
import Synth.Basic
import Synth.EagerFeatures
import Synth.LazyFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.Context

-- TODO
synthDimsWithTile :: StdGoal -> SolveM (ForTest Dims)
synthDimsWithTile (Goal inputs outputs ctx) = do
  features <- lift . precompute . choice "synthDimsWithTile" $ [
    ("grid", LazyFeatures.choose $ getBasicLazyFeatures inputs),
    ("tile", do
      phi   <- oneOf "tilePred" [("eq", (==)), ("eqOrBlank2", eqOrBlank2)]
      deltas <- oneOf "deltas" [("[0]", [0])]
      tDatas <- liftO $ Ex.mapM (Tile.findMinimalTilePred deltas phi) inputs
      LazyFeatures.choose $ getBasicLazyFeatures tDatas)
    ]

  find1E "synthInts2Dims" $ synthInts2Dims $ ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) (map Grid.dims outputs)

synthDims :: StdGoal -> SolveM (ForTest Dims)
synthDims (Goal inputs outputs ctx) = do
  features <- lift . precompute . choice "synthDims" $ [
    -- Too weak for feca:
    --("dims", LazyFeatures.choose $ getBasicLazyFeatures (Ex.map Grid.dims inputs))
    ("grid", LazyFeatures.choose $ getBasicLazyFeatures inputs)
    ]

  find1E "synthInts2Dims" $ synthInts2Dims $ ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) (map Grid.dims outputs)

canSynthDims :: StdGoal -> SolveM Bool
canSynthDims (Goal inputs outputs ctx) = do
  features <- lift . precompute . choice "synthDims" $ [
    ("grid", LazyFeatures.choose $ getBasicLazyFeatures inputs)
    ]
  dims <- find1O "canSynthDims" $ synthInts2Dims $ ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) (map Grid.dims outputs)
  pure $ Maybe.isJust dims

-- TODO: Is it a Rect2Rect problem? Hard to tell without passing an actual SPEC
synthRect :: StdGoal -> ForTrain Rect -> SolveM (ForTest Rect)
synthRect (Goal inputs _ ctx) outRects = do
  inRects  <- liftO $ Ex.mapM Grid.nonBlankRect inputs
  features <- lift . precompute $ choice "synthRect" [
    ("inRect", LazyFeatures.choose $ getBasicLazyFeatures inRects),
    ("grid",   LazyFeatures.choose $ getBasicLazyFeatures inputs)
    ]
  find1E "synthInts2Rect" $ synthInts2Rect $ ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) outRects

synthTileData :: Synth1Context -> Ex (Grid Color) -> ForTrain TileData -> SolveM (ForTest TileData)
synthTileData ctx inputs outDatas = do
  features <- lift . precompute . choice "synthTileData" $ [
    ("dims", LazyFeatures.choose $ getBasicLazyFeatures (Ex.map Grid.dims inputs)),
    ("tile", do
      phi   <- oneOf "tilePred" [("eq", (==)), ("eqOrBlank2", eqOrBlank2)]
      deltas <- oneOf "deltas" [("[0]", [0]), ("[-1,1]", [-1, 1])]
      tDatas <- liftO $ Ex.mapM (Tile.findMinimalTilePred deltas phi) inputs
      LazyFeatures.choose $ getBasicLazyFeatures tDatas)
    ]
  find1E "synthInts2TileData" $ synthInts2TileData $ ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) outDatas
