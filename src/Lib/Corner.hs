-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Lib.Corner where

import Lib.HasElems
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims

import Lib.Index (Index(..))
import qualified Lib.Index as Index

import Synth1.Basic
import Search.SearchT

data Corner = TopRight | TopLeft | BottomRight | BottomLeft deriving (Eq, Ord, Show)

isTop :: Corner -> Bool
isTop TopRight = True
isTop TopLeft = True
isTop BottomRight = False
isTop BottomLeft = False

isBottom :: Corner -> Bool
isBottom TopRight = False
isBottom TopLeft = False
isBottom BottomRight = True
isBottom BottomLeft = True

isLeft :: Corner -> Bool
isLeft TopRight = False
isLeft TopLeft = True
isLeft BottomRight = False
isLeft BottomLeft = True

isRight :: Corner -> Bool
isRight TopRight = True
isRight TopLeft = False
isRight BottomRight = True
isRight BottomLeft = False

cornerIdx :: Dims -> Corner -> Index
cornerIdx dims TopLeft = Index 0 0
cornerIdx (Dims m n) TopRight = Index 0 (n - 1)
cornerIdx (Dims m n) BottomLeft = Index (m - 1) 0
cornerIdx (Dims m n) BottomRight = Index (m - 1) (n - 1)

isCorner :: Dims -> Index -> Bool
isCorner dims idx = flip any elems $ \corn -> idx == (cornerIdx dims corn)

instance HasElems Corner where
  elems = [TopRight, TopLeft, BottomRight, BottomLeft]

instance (Monad m) => HasEnumVals m Corner where
  enumVals = oneOf "Corner.enumVals" [
    ("TopLeft",   TopLeft),
    ("TopRight", TopRight),
    ("BottomRight",  BottomRight),
    ("BottomLeft",   BottomLeft)
    ]

instance (Monad m) => HasEnumVals m [Corner] where
  enumVals = choice "Axis.enumVals" [
    ("top",      pure $ [TopRight, TopLeft])
    , ("bottom",  pure $ [BottomRight, BottomLeft])
    , ("downRight",  pure $ [TopLeft, BottomRight])
    , ("downLeft",  pure $ [TopRight, BottomLeft])
    , ("single", do
          corn <- enumVals
          pure $ [corn]
      )
    ]
