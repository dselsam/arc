-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Features where

import Synth1.Synth1Context
import Debug.Trace
import Util.Imports
import qualified Util.Int as Int
import qualified Lib.Axis as Axis
import Lib.Blank
import Data.Maybe (isJust)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Vector.Unboxed.Base (Unbox)
import Data.Monoid (mempty)
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Util.List (uncurry3)
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Data.List as List
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import Synth.Ex (Ex(..))
import qualified Synth.Ex as Ex
import Lib.Color
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.Axis
import Synth1.Basic
import Search.SearchT
import Lib.Grid (Grid)
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import Lib.Symmetry (enumReasonableSymmetries, Symmetry (..), enumProperSymmetries, eqUptoSymmetry)
import Search.DFS
import qualified Lib.Shape as Shape
import Lib.Shape (values, enclosingRect, isFilledRect, values, enclosingRect, isFilledRect, values, enclosingRect, isFilledRect, Shape)
import qualified Lib.Rect as Rect
import Lib.Rect (Rect)
import qualified Lib.Parse as Parse

import Debug.Trace

instance (Monad m, Unbox a, Eq a, Ord a, HasBlank a) => HasBasicLazyFeatures m (Grid a) Bool where
  -- TODO: more here or maybe leave it to more advanced?
  getBasicLazyFeatures gs = LazyFeatures $ choice "Grid.getBasicLazyFeatures.Bool" [
    ("dims",      LazyFeatures.choose $ getBasicLazyFeatures (Ex.map Grid.dims gs)),
    ("symmetric", do
        sym <- Symmetry.enumProperSymmetries
        pure $ Ex.map (\g -> Symmetry.eqUptoSymmetry g sym g) gs)
    ]

instance (Monad m, Unbox a, Eq a, Ord a, HasBlank a) => HasBasicLazyFeatures m (Grid a) Int where
  -- TODO: more here or maybe leave it to more advanced?
  getBasicLazyFeatures gs = LazyFeatures $ choice "Grid.getBasicLazyFeatures.Int" [
    ("dims",                  LazyFeatures.choose $ getBasicLazyFeatures (Ex.map Grid.dims gs)),
    ("nNonBlankVals",         pure $ Ex.map Grid.nNonBlankVals gs),
    ("nDistinctNonBlankVals", pure $ Ex.map (Grid.nDistinctVals nonBlank) gs),
    ("maxValCount",           pure $ Ex.map (Grid.maxValCount nonBlank) gs)
    ]

instance (Monad m) => HasBasicLazyFeatures m (Grid Color) Color where
  -- TODO: more here or maybe leave it to more advanced?
  getBasicLazyFeatures gs = LazyFeatures $ choice "Grid.getBasicLazyFeatures.Color" [
    ("pickColor", do f <- Grid.pickColor; flip Ex.mapM gs $ liftO . f)
   ]

-- instance (Monad m) => HasBasicLazyFeatures m (Grid Color) Color where
--   -- TODO: more here or maybe leave it to more advanced?
--   getBasicLazyFeatures gs = LazyFeatures $ choice "Grid.getBasicLazyFeatures.Color" [
--     ("majority", liftO $ Ex.mapM Grid.majorityNonBlankVal gs),
--     ("minority", liftO $ Ex.mapM Grid.minorityNonBlankVal gs)
--     ]

instance (Monad m) => HasEnumBoolFeatures m (Grid Color) where
  enumBoolFeatures = choice "Grid.enumBoolFeatures" [
    ("dims",              do { dims2bool <- enumBoolFeatures; pure $ \g -> dims2bool (Grid.dims g) }),
    ("isUniform",         pure $ isJust . Grid.isUniform),
    ("isSymmetricAround", do { v <- enumVals; pure $ Grid.isSymmetricAround v })
    ]

instance (Monad m) => HasEnumIntFeatures m (Grid Color) where
  enumIntFeatures = choice "Grid.enumIntFeatures" [
    ("dims",              do { dims2int <- enumIntFeatures; pure $ \g -> dims2int (Grid.dims g) }),
    ("nNonBlankVals",         pure $ Grid.nNonBlankVals),
    ("nDistinctNonBlankVals", pure $ Grid.nDistinctVals nonBlank)
    ]

instance (Monad m, HasSynth1Context m Color) => HasEnumReduceFeatures m Grid Color where
  enumReduceFeatures = choice "Grid.enumReduceFeatures" [
    -- TODO: see comment at `class HasEnumReduceFeatures` about optional features and where
    -- the failure should live.
    ("majorityNonBlankVal",    Ex.map (\_ -> \g -> let (x:_, _) = Grid.majorityNonBlankVals g in x) <$> getDummyEx),
    ("color",                  Ex.map (\c -> \_ -> c) <$> enumColorsCtx)
    ]

instance (Monad m, HasSynth1Context m Color) => HasEnumUnaryOps m (Grid Color) where
  enumUnaryOps = choice "Grid.enumUnaryOps" [
    -- TODO: swap colors, shift-cyclic, whatever
    ("id",         Ex.map (\_ -> id) <$> getDummyEx),
    ("stripColor", do
        cs <- enumColorsCtx
        pure $ Ex.map (\c -> Grid.map (\_ x -> if x == c then blank else x)) cs),
    ("dye",        do
        cs <- enumColorsCtx
        pure $ Ex.map (\c -> Grid.map (\_ x -> if nonBlank x then c else blank)) cs)
    ]

-- TODO: could generalize
-- TODO: context?
-- TODO: factor: sample binOp, sample Dop
-- TODO: skip level 1 and worry about colors later?
instance (Monad m, HasSynth1Context m Color) => HasEnumBinOps m (Grid Color) where
  enumBinOps = choice "Grid.enumBinOps" [
    ("or",       Ex.map (\_ -> Grid.mapBinOp Blank.or) <$> getDummyEx),
    ("blank1",   do
        f <- enumBinOpD
        Ex.map (\_ -> Grid.map3Op1 f) <$> getDummyEx),
    ("blankCtx", do
        f <- enumBinOpD
        Ex.map (\c -> Grid.mapBinOp (f c)) <$> enumColorsCtx)
    ]
    where
      enumBinOpD = oneOf "enumBinOpD" [("orD",   Blank.orD),
                                       ("norD",  Blank.norD),
                                       ("andD",  Blank.andD),
                                       ("nandD", Blank.nandD),
                                       ("xorD",  Blank.xorD),
                                       ("nxorD", Blank.nxorD)]

--instance (Monad m) => HasReduceBinOps m Grid a where
--  enumReduceBinOps = choice "Grid.enumReduceBinOps" [
--    ("reduceBinOp", pure Grid.reduceBinOp)
--    ]

-- shapeIsGenusZero :: (Eq a, Ord a, Unbox a, HasBlank a, Show a) => Shape a -> Bool -- only works for convex shapes
-- shapeIsGenusZero shape = isJust $ do
--   guard . not . null $ Shape.idx2val shape
--   let rect = Shape.enclosingRect shape
--   let sortedIndices = List.sortBy (\(Index i j) (Index i1 j1) -> compare i i1) (Map.keys $ Shape.idx2val shape)
--   let groupedIndices = List.groupBy (\(Index i j) (Index i1 j1) -> i == i1) sortedIndices
--   let isInterval idxs =
--         let sorted = List.sortBy (\(Index i j) (Index i1 j1) -> compare j j1) idxs
--             leastCol = Index.col . head $ sorted
--             maxCol = Index.col . last $ sorted in
--         length idxs == maxCol - leastCol + 1
--   let obstructionMask = isInterval <$> groupedIndices
--   pure ()

rectHoles :: (Unbox a, Ord a, Eq a, HasBlank a) => Shape a -> Int
rectHoles shape =
  let rect = Shape.enclosingRect shape
      grid = Grid.fromShapes (Rect.dims rect) [Shape.normalize shape]
      blankShapes = Parse.parseShapesLocal grid (\_ -> isBlank)  (\ax _ _ -> Axis.isOrtho ax) in
  length $ flip filter blankShapes $ \blankShape ->
    let blankShapeRect = Shape.enclosingRect blankShape
        framedBlankShapeRect = Rect.addFrame blankShapeRect in
      Grid.rectInBounds grid framedBlankShapeRect &&
        Shape.isFilledRect blankShape &&
          (flip all (Rect.getPerimeterIdxs framedBlankShapeRect) $ nonBlank . Grid.get grid)

-- instance (Monad m, Eq a, Ord a, HasEnumVals m a, Unbox a, HasBlank a, Show a) => HasEnumIntFeatures m (Shape a) where
instance (Monad m) => HasEnumIntFeatures m (Shape Color) where
  enumIntFeatures = choice "Shape.enumIntFeatures" [
    ("nDistinctVals",  pure Shape.nDistinctVals),
    ("nPoints",        pure Shape.nPoints),
    ("rectDiff",       pure $ \s -> Rect.area (enclosingRect s) - Shape.nPoints s),
    ("rect",     do { rect2int <- enumIntFeatures; pure $ rect2int . enclosingRect }),
    ("counts",   do { v <- enumVals; pure $ \s -> length . List.filter (==v) $ Shape.valuesToList s }),
    ("rectHoles", pure $ rectHoles)
    ]

-- instance (Monad m, Eq a, Ord a, HasEnumVals m a, Unbox a, HasBlank a, Show a) => HasBasicLazyFeatures m (Shape a) Int where
instance (Monad m) => HasBasicLazyFeatures m (Shape Color) Int where
  getBasicLazyFeatures shapes = LazyFeatures $ flip Ex.map shapes <$> enumIntFeatures

isSymmetricAtAllShape :: (Monad m, Eq a, Ord a, Unbox a, HasBlank a) => SearchT m (Shape a -> Bool)
isSymmetricAtAllShape = do
  properSymmetries <- lift . precompute $ enumProperSymmetries
  pure $ \shape ->
    if Shape.nPoints shape <= 1 then False else
    flip any properSymmetries $ \(_, sym) ->
      let g = Grid.fromShapes (Rect.dims . Shape.enclosingRect $ shape) [Shape.normalize shape] in
        eqUptoSymmetry g sym g

isSymmetricShape :: (Monad m, Eq a, Ord a, Unbox a, HasBlank a) => SearchT m (Shape a -> Bool)
isSymmetricShape = do
  syms <- enumReasonableSymmetries
  pure $ \shape ->
    if Shape.nPoints shape <= 1 then False else
      let g = Grid.fromShapes (Rect.dims . Shape.enclosingRect $ shape) [Shape.normalize shape] in
        flip all syms $ \sym -> eqUptoSymmetry g sym  g

-- TODO: some features requires dimension information, suggesting that
-- we would need these typeclasses to allow context types.
instance (Monad m, Eq a, Ord a, HasEnumVals m a, Unbox a, HasBlank a) => HasEnumBoolFeatures m (Shape a) where
  enumBoolFeatures = choice "Shape.enumBoolFeatures" [
    ("isPoint"             ,   pure $ \s -> Shape.nPoints s == 1),
    ("isUniform",     pure Shape.isUniform),
    ("hasValue",      do { v <- enumVals; pure $ \s -> Set.member v (values s) }),
    ("isOrthoLine"         ,   pure $ \s -> Shape.isOrthoLine s),
    ("isFilledRectNotLine ",   pure $ \s -> Shape.isFilledRect s && not (Shape.isOrthoLine s)),
    ("containsFrame", pure Shape.containsFrame),
    ("rect",          do { rect2bool <- enumBoolFeatures; pure $ rect2bool . enclosingRect }),
    ("isFilledRectNotPoint",  pure $ \s -> Shape.isFilledRect s && Shape.nPoints s > 1),
    ("noHoles", pure $ \s -> rectHoles s == 0),
    ("oneHole", pure $ \s -> rectHoles s == 1),
    ("gt1Hole", pure $ \s -> rectHoles s > 1),
    ("isSymmetric", isSymmetricShape),
    ("isSymmetricAtAll", isSymmetricAtAllShape)
    -- ("enumIntBoolFeatures", enumIntBoolFeatures) -- ????
    ]

instance (Monad m, Eq a, Ord a, HasEnumVals m a, Unbox a, HasBlank a) => HasBasicLazyFeatures m (Shape a) Bool where
  getBasicLazyFeatures shapes = LazyFeatures $ flip Ex.map shapes <$> enumBoolFeatures
