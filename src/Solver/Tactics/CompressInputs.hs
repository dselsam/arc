-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.CompressInputs (compressInputs) where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import Data.List
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Util.Int as Int
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import qualified Lib.Symmetry as Symmetry
import Lib.Symmetry (Symmetry)
import Solver.Tactics.GuessDims
import Synth1.Basic
import Lib.Blank
import Synth1.Arith
import Search.DFS
import Lib.Tile (TileData(..))
import qualified Lib.Tile as Tile

-- Motivation:
--   - d8c310e9
--   - caa06a1f
--   - 963e52fc
-- Does not handle:
--   - the one with the two criss-crossing polka-dotted lines (would require *collapsing*)

compressInputs :: StdGoal -> SolveM TacticResult
compressInputs goal@(Goal inputs outputs ctx) = find1 "compressInputs" $ do
  -- TODO: this fails on 8eb1be9a for several reasons
  -- TODO: do we really need or want both options?
  phi <- choice "compressInputs" [
    ("eq",         pure (==)),
    ("eqOrBlank2", pure eqOrBlank2)
    ]
  deltas <- oneOf "deltas" [("[0]", [0]), ("[-1,1]", [-1, 1])]
  tDatas <- liftO $ Ex.mapM (Tile.findMinimalTilePred deltas phi) inputs
  let keepDims = Ex.map Tile.dims tDatas
  let newInputs = Ex.map (\(dims, input) -> Grid.getSubgridUnsafe input dims (Index 0 0)) (Ex.zip keepDims inputs)
  pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure
