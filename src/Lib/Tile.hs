-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData #-}
module Lib.Tile where

import Util.Imports
import Data.Vector.Unboxed.Base (Unbox)
import Search.SearchT
import Synth1.Basic
import Synth1.Basic
import Search.DFS
import Lib.Grid (Grid)
import Lib.Blank
import Lib.Features
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Util.List as List
import Synth.Spec (Spec, SynthFn, SynthFn1)
import qualified Synth.Spec as Spec
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Search.DFS (find1)
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Synth.Ints2Int (synthInts2IntE)
import qualified Data.Map as Map

data TileData = TileData { dims :: Dims, delta :: Int } deriving (Eq, Ord, Show)

-- TODO: remove once we handle Maybe features correctly
dummy = TileData (Dims 0 0) 0

applyIndex :: TileData -> Index -> Index
applyIndex (TileData (Dims tx ty) dlta) (Index x y) =
  Index (mod (x + y * dlta) tx) (mod y ty)

isTiling :: (Unbox a) => (a -> a -> Bool) -> Grid a -> TileData -> Bool
isTiling p g tData = Dims.all (Grid.dims g) $ \idx ->
  p (Grid.get g (applyIndex tData idx)) (Grid.get g idx)

getTilingDictWith :: (Unbox a) => (a -> a -> Bool) -> Grid a -> TileData -> (a -> a -> a) -> Maybe (Map Index a)
getTilingDictWith p g tData reducer = Dims.iterM (Grid.dims g) Map.empty $ \acc idx ->
  let tileIdx = (applyIndex tData idx)
      c       = Grid.get g idx
  in
  case Map.lookup tileIdx acc of
    Nothing -> pure $ Map.insert tileIdx c acc
    Just v -> do
      guard $ p v c
      pure $ Map.insert tileIdx (reducer c v) acc

apply :: (Unbox a, Eq a) => Grid a -> TileData -> Dims -> Grid a
apply g tData newDims = Grid.fromFunc newDims $ \idx ->
  Grid.get g (applyIndex tData idx)

findMinimalTilePred :: (Unbox a) => [Int] -> (a -> a -> Bool) -> Grid a -> Maybe TileData
findMinimalTilePred deltas p g =
  flip List.first [1..Grid.nCols g] $ \n ->
    flip List.first [1..Grid.nRows g] $ \m -> do
      guard $ m < Grid.nRows g || n < Grid.nCols g
      flip List.first deltas $ \delta -> do
        let tData = TileData (Dims m n) delta
        guard $ isTiling p g tData
        pure $ tData

findMinimalTilePredDict :: (Unbox a) => [Int] -> (a -> a -> Bool) -> Grid a -> (a -> a -> a) -> Maybe (TileData, Map Index a)
findMinimalTilePredDict deltas p g reducer =
  flip List.first [1..Grid.nCols g] $ \n ->
    flip List.first [1..Grid.nRows g] $ \m -> do
      guard $ m < Grid.nRows g || n < Grid.nCols g
      flip List.first deltas $ \delta -> do
        let tData = TileData (Dims m n) delta
        ((,) tData) <$> getTilingDictWith p g tData reducer
  

splitTileData :: (Unbox a) => Grid a -> TileData -> [TileData]
splitTileData g tData@(TileData (Dims x y) d)
  | d /= 0 = [tData]
  | x < Grid.nRows g && y < Grid.nCols g = [
      TileData (Dims (Grid.nRows g) y) d,
      TileData (Dims x (Grid.nCols g)) d,
      tData]
  | otherwise = [tData]

---------------------------------------
-- Instances
---------------------------------------

instance (Monad m) => HasBasicLazyFeatures m TileData Int where
  getBasicLazyFeatures tds = LazyFeatures $ choice "TileData.getBasicLazyFeatures.Int" [
    ("dims",  LazyFeatures.choose $ getBasicLazyFeatures (Ex.map dims tds)),
    ("delta", pure (Ex.map delta tds))
    ]
