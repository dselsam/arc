-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Lib.Rotation where

import Lib.HasElems
import Lib.Dims (Dims(..))
import qualified Lib.Dims as Dims

import Lib.Index (Index(..))
import qualified Lib.Index as Index
import Lib.Axis
import Synth1.Basic
import Search.SearchT

data Rotation  = Clockwise | Counterclockwise   deriving (Eq, Ord, Show)

rotateAround dims Clockwise        = Index.transpose . reflectAround dims Horizontal
rotateAround dims Counterclockwise = Index.transpose . reflectAround dims Vertical

instance (Monad m) => HasEnumVals m Rotation where
  enumVals = oneOf "Rotation.enumVals" [
    ("clockwise",        Clockwise),
    ("counterclockwise", Counterclockwise)
    ]
