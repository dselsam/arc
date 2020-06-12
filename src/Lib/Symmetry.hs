-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib.Symmetry where

import Debug.Trace
import Util.Imports
import Lib.Axis
import qualified Lib.Axis as Axis
import Lib.Rotation
import Lib.Grid
import qualified Lib.Index as Index
import Synth1.Basic
import Search.SearchT
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import Data.Vector.Unboxed.Base (Unbox)
import qualified Data.List as List
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving

data Symmetry = SymIdentity | SymReflect Axis | SymRotateCW Int | SymCyclicShift Index deriving (Eq, Ord, Show)

isReflect sym = case sym of
  SymReflect _ -> True
  _ -> False

applyIndex :: Dims -> Symmetry -> Maybe (Index -> Index)
applyIndex dims SymIdentity = pure id
applyIndex dims (SymReflect ax)
  | isOrtho ax  = Just $ Axis.reflectAround dims ax
  | otherwise   = do
      guard $ Dims.isSquare dims
      pure $ Axis.reflectAround dims ax
applyIndex dims (SymRotateCW k)
  | k == 2 = do
      pure $ rotateAround (Dims.transpose dims) Clockwise . rotateAround dims Clockwise
  | k == 1 || k == 3 = do
      guard $ Dims.isSquare dims
      let f = rotateAround dims Clockwise
      pure $ \idx -> iterate f idx List.!! k

applyIndex (Dims m n) (SymCyclicShift (Index dx dy)) = pure $ \(Index x y) ->
  Index (mod (x + dx) m) (mod (y + dy) n)

applyIndex _ _ = Nothing

-- g1 == sym g2
eqUptoSymmetryOpt :: (Unbox a, Eq a) => Grid a -> Symmetry -> Grid a -> Maybe Bool
eqUptoSymmetryOpt g1 sym g2 = do
  guard $ Grid.dims g1 == Grid.dims g2
  encode2 <- applyIndex (Grid.dims g1) sym
  pure $ Dims.all (Grid.dims g1) $ \idx -> Grid.get g1 idx == Grid.get g2 (encode2 idx)

-- Just a convenience, for callers who don't want to plumb the maybe
eqUptoSymmetry :: (Unbox a, Eq a) => Grid a -> Symmetry -> Grid a -> Bool
eqUptoSymmetry g1 sym g2 = case eqUptoSymmetryOpt g1 sym g2 of
  Nothing -> False
  Just b -> b

apply :: (Unbox a) => Symmetry -> Grid a -> Maybe (Grid a)
apply SymIdentity g = pure g
apply sym g = do
  idx2idx <- applyIndex (Grid.dims g) sym
  pure $ Grid.fromFunc (Grid.dims g) $ Grid.get g . idx2idx

applyMany :: (Unbox a) => [Symmetry] -> Grid a -> Maybe (Grid a)
applyMany [] g = pure g
applyMany (sym:syms) g = apply sym g >>= applyMany syms

enumAllSymmetries :: (Monad m) => SearchT m Symmetry
enumAllSymmetries = choice "enumAllSymmetries" [
  ("identity", pure SymIdentity),
  ("proper", enumProperSymmetries)
  ]

enumProperSymmetries :: (Monad m) => SearchT m Symmetry
enumProperSymmetries = choice "enumProperSymmetries" [
    ("reflect", SymReflect <$> enumVals),
    ("rotate",  SymRotateCW <$> enumListElems [1, 2, 3]),
    ("cycle",   do
        -- Note: general version is dimension specific
        dx <- enumListElems [-1, 0, 1]
        dy <- enumListElems [-1, 0, 1]
        guard $ dx /= 0 || dy /= 0
        pure $ SymCyclicShift (Index dx dy))
    ]

-- TODO: make it clear in the name that it returns a SET
enumReasonableSymmetries :: (Monad m) => SearchT m [Symmetry]
enumReasonableSymmetries =
  choice "enumReasonableSymmetries"
    [
      ("ortho",     pure [SymReflect Horizontal, SymReflect Vertical]),
      ("singleton", pure <$> enumProperSymmetries),
      ("rotational", pure $ (SymRotateCW <$> [1,2,3]))
    ]
