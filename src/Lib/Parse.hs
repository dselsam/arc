-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Parse where

import Data.Vector.Unboxed.Base (Unbox)
import Debug.Trace
import Lib.Blank
import Lib.Color
import Util.Imports
import qualified Util.List as List
import qualified Util.Map as Map
import qualified Data.Maybe as Maybe
import qualified Lib.Index as Index
import Lib.Axis (Axis(..))
import qualified Lib.Axis as Axis
import Synth1.Basic
import Search.SearchT
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import qualified Data.List as List
import qualified Lib.Dims as Dims
import qualified Lib.BGrid as Box
import Lib.Grid (Grid)
import qualified Lib.Grid as Grid
import qualified Data.Map as Map
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import qualified Data.UnionFind.ST as UnionFind
import Data.UnionFind.ST (Point)
import Lib.HasElems
import Control.Monad.ST
import Data.STRef

parseShapesLocal :: (Unbox a) => Grid a -> (Index -> a -> Bool) -> (Axis -> a -> a -> Bool) -> [Shape a]
parseShapesLocal g keep union = runST $ do
  points :: Box.Grid (Maybe (Point s Index)) <- Box.fromFuncM (Grid.dims g) $ \idx -> do
    let x = Grid.get g idx
    if keep idx x
      then Just <$> UnionFind.fresh idx
      else pure Nothing

  Dims.iterM (Grid.dims g) () $ \_ idx1 -> do
    case Box.get points idx1 of
      Nothing -> pure ()
      Just p1 -> do
        for_ elems $ \ax -> do
          let idx2 = idx1 + Axis.toDelta ax
          when (Dims.inBounds (Grid.dims g) idx2
                && keep idx2 (Grid.get g idx2)
                && union ax (Grid.get g idx1) (Grid.get g idx2)) $ do
            -- Safe because `keep <-> isJust`
            let p2 = Maybe.fromJust $ Box.get points idx2
            UnionFind.union p1 p2

  root2shape <- Dims.iterM (Box.dims points) Map.empty $ \shapes idx ->
    case Box.get points idx of
      Nothing -> pure shapes
      Just p -> do
        root <- UnionFind.descriptor p
        pure $ Map.insertWith Shape.union root (Shape.singleton idx $ Grid.get g idx) shapes

  pure $ Map.elems root2shape

parseShapesGlobalKey :: (Unbox a) => Grid a -> (Index -> a -> Maybe Int) -> [Shape a]
parseShapesGlobalKey g key = Map.elems $ Dims.iter (Grid.dims g) Map.empty $ \acc idx -> pure $
  case key idx (Grid.get g idx) of
    Nothing -> acc
    Just k -> Map.insertWith Shape.union k (Shape.singleton idx (Grid.get g idx)) acc

data ColorOptions = ParseNoBlanksByColor | ParseNoBlanksAny | ParseOnlyBlanks deriving (Eq, Ord, Show)
data ParseKind    = ParseLocalNone | ParseLocalOrtho      | ParseLocalAny    | ParseLocalH | ParseLocalV | ParseGlobal deriving (Eq, Ord, Show)

data Options = Options {
  kind  :: ParseKind,
  color :: ColorOptions
  } deriving (Eq, Ord, Show)

parseScene :: Grid Color -> Options -> [Shape Color]
parseScene g (Options ParseLocalNone  ParseNoBlanksByColor) = parseShapesLocal     g (\_ -> nonBlank) (\_ _ _ -> False)
parseScene g (Options ParseLocalOrtho ParseNoBlanksByColor) = parseShapesLocal     g (\_ -> nonBlank) (\ax x y -> Axis.isOrtho ax && x == y)
parseScene g (Options ParseLocalOrtho ParseNoBlanksAny)     = parseShapesLocal     g (\_ -> nonBlank) (\ax _ _ -> Axis.isOrtho ax)
parseScene g (Options ParseLocalOrtho ParseOnlyBlanks)      = parseShapesLocal     g (\_ -> isBlank)  (\ax _ _ -> Axis.isOrtho ax)
parseScene g (Options ParseLocalAny   ParseNoBlanksByColor) = parseShapesLocal     g (\_ -> nonBlank) (\_ x y -> x == y)
parseScene g (Options ParseLocalAny   ParseNoBlanksAny)     = parseShapesLocal     g (\_ -> nonBlank) (\_ _ _ -> True)
parseScene g (Options ParseLocalAny   ParseOnlyBlanks)      = parseShapesLocal     g (\_ -> isBlank)  (\_ _ _ -> True)
parseScene g (Options ParseLocalH     ParseNoBlanksByColor) = parseShapesLocal     g (\_ -> nonBlank)  (\ax x y -> ax == Horizontal && x == y)
parseScene g (Options ParseLocalV     ParseNoBlanksByColor) = parseShapesLocal     g (\_ -> nonBlank)  (\ax x y -> ax == Vertical && x == y)
parseScene g (Options ParseGlobal     ParseNoBlanksByColor) = parseShapesGlobalKey g $ \_ x -> do { guard (nonBlank x); pure (toNat x) }
parseScene g (Options ParseGlobal     ParseNoBlanksAny)     = parseShapesGlobalKey g $ \_ x -> do { guard (nonBlank x); pure 0 }
parseScene g (Options ParseGlobal     ParseOnlyBlanks)      = parseShapesGlobalKey g $ \_ x -> do { guard (isBlank x); pure 0 }
