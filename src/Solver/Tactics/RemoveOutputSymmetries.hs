-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.RemoveOutputSymmetries (removeOutputSymmetries) where

import Util.Imports
import qualified Lib.BGrid as Box
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
import Search.SearchT
import Synth1.Basic
import Synth1.Arith
import Search.DFS (enumAll, find1)
import Lib.Tile (TileData(..))
import qualified Lib.Tile as Tile

data ROSOptions = ROSOptions {
  minShrinkWhenSameSize :: Float
  } deriving (Eq, Ord, Show)

defaultROSOptions = ROSOptions { minShrinkWhenSameSize = 0.5 }

removeOutputSymmetries goal = choice "removeOutputSymmetries" [
  ("partialTile",  partialTile goal),
  ("fixedPattern", fixedPattern goal)
  ]

-- Note: we currently make a bad guess on caa06a1f, since we assume it is always a 2x1 tiling
-- The input feature would work but only after stripping the green/blue/fuschia as background
partialTile goal@(Goal inputs outputs ctx) = find1 "partialTile" $ do
  testDims <- synthDims goal -- we don't need it yet but need to know that we can guess
  -- TODO: this would need to be a *guardMost* to get d631b094
  deltas <- oneOf "deltas" [("[0]", [0]), ("[-1,1]", [-1, 1])]
  tDatas <- liftO $ mapM (Tile.findMinimalTilePred deltas (==)) outputs

  -- TODO: guard that if it divide before, it better divide now

  -- motivated by problems like a57
  guard $ flip all (zip3 (Ex.train inputs) outputs tDatas) $ \(input, output, TileData dims delta) ->
    (Grid.sameDims input output) <= (fromIntegral (Dims.nCells dims) <= fromIntegral (Dims.nCells (Grid.dims input)) * minShrinkWhenSameSize defaultROSOptions)

  -- TODO: sanity check this. seems weird that the guard was on the inputs before.
  guard $ flip any (zip outputs tDatas) $ \(output, TileData dims delta) -> dims /= Grid.dims output
  guard $ flip any (zip outputs tDatas) $ \(output, TileData dims delta) -> Dims.nRows dims + 1 /= Grid.nRows output
  guard $ flip any (zip outputs tDatas) $ \(output, TileData dims delta) -> Dims.nCols dims + 1 /= Grid.nCols output

  tDatas <- oneOf "tileData" [(show tDatas, tDatas)]

  -- Don't bother with this
  -- tDatas <- mapM enumListElems $ map (uncurry Tile.splitTileData) (zip outputs tDatas)
  -- liftIO . traceIO $ "[partialTile] synthing TileDatas: " ++ show tDatas

  testTileDatas <- synthTileData ctx inputs tDatas
  guard $ all (\tData -> Tile.delta tData `elem` deltas) testTileDatas
  for_ (zip testDims testTileDatas) $ \(dims, tData) ->
    unless (Dims.nRows (Tile.dims tData) <= Dims.nRows dims && Dims.nCols (Tile.dims tData) <= Dims.nCols dims) $ do
      checksum <- lift $ asks ctxChecksum
      liftIO . traceIO $ "[partialTile] " ++ show checksum ++ " tile bigger than guess-dims: " ++ show (tData, dims)
      deadend "see above"
  let newOutputs = map (\(tData, output) -> Grid.getSubgridUnsafe output (Tile.dims tData) (Index 0 0)) (zip tDatas outputs)

  let reconstruct :: ForTest (Grid Color) -> MaybeT IO (ForTest (Grid Color))
      reconstruct guesses = flip mapM (zip3 testTileDatas testDims guesses) $ \(tData, dims, guess) -> do
        unless (Tile.dims tData == Grid.dims guess) $
          liftIO . traceIO $ "[partialTile] reconstruct fail: " ++ show (Tile.dims tData, Grid.dims guess)
        guard $ Tile.dims tData == Grid.dims guess
        pure $ Tile.apply guess tData dims
  pure $ TacticResult.Decompose (Goal inputs newOutputs ctx) reconstruct

fixedPattern goal@(Goal inputs outputs ctx) = do
  (Dims mOuter nOuter, symmetries) <- liftO $ detectTrainSymmetries outputs
  let encode g = let Dims mOrig nOrig = Grid.dims g in
                   Grid.getSubgridUnsafe g (Dims (div mOrig mOuter) (div nOrig nOuter)) (Index 0 0)
  let decode guess = MaybeT . pure $ do
        gs <- Box.fromFuncM (Box.dims symmetries) (\idx -> Symmetry.apply (Box.get symmetries idx) guess)
        Grid.unpartitionEven gs
  pure $ TacticResult.Decompose (Goal inputs (map encode outputs) ctx) (mapM decode)
  where
    detectTrainSymmetries :: ForTrain (Grid Color) -> Maybe (Dims, Box.Grid Symmetry)
    detectTrainSymmetries outputs = do
      -- higher numbers correspond to more tiling, and so more compression
      let mOuters = sortOn (\k -> -k) . Int.allCommonDivisors . map Grid.nRows $ outputs
      let nOuters = sortOn (\k -> -k) . Int.allCommonDivisors . map Grid.nCols $ outputs
      -- style preference to try columns before rows
      flip List.first nOuters $ \n ->
        flip List.first mOuters $ \m -> do
          guard $ m > 1 || n > 1
          syms :: Box.Grid Symmetry <- computeSymmetryGrids (Dims m n) outputs
          pure (Dims m n, syms)

    computeSymmetryGrids dims@(Dims m n) outputs = do
      allSymmetries :: [Symmetry] <- enumAll $ Symmetry.enumAllSymmetries
      okSymmetries :: ForTrain (Box.Grid [Symmetry]) <- flip mapM outputs $ \output -> do
        pOutputs <- Grid.partitionEvenOuterDims dims output
        let template = Box.get pOutputs (Index 0 0)
        pure $ Box.fromFunc dims $ \idx -> flip filter allSymmetries $ \sym ->
          Symmetry.eqUptoSymmetry (Box.get pOutputs idx) sym template
      let alwaysOkSymmetries :: Box.Grid [Symmetry] = List.reduce (\syms1 syms2 -> Box.fromFunc (Box.dims syms1) $ \idx ->
                                                                  intersect (Box.get syms1 idx) (Box.get syms2 idx)) id okSymmetries
      flip Box.mapM alwaysOkSymmetries $ \_ syms -> do
        guard $ not . null $ syms
        pure $ head syms
