-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib.Color where

import Data.Default (def)
import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Synth.Ex (Ex(..))
import Util.Imports
import qualified Synth.Ex as Ex
import Synth1.Synth1Context
import Search.SearchT
import Synth1.Basic
import Lib.Blank
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving
import qualified Util.List as List

{-
data Color = Black | Blue | Red | Green | Yellow | Grey | Fuschia | Orange | Teal | Brown
  | ColorTrue -- our own, indicating a "bit" that is true
  deriving (Eq, Ord, Generic)
-}

newtype Color = Color Int deriving (Eq, Ord, Generic, Num)
instance NFData Color

derivingUnbox "Color"
    [t|  Color -> Int |]
    [| \(Color c) -> c |]
    [| \c -> Color c |]

instance HasBlank Color where
  blank = Color 0
{-
-- TODO: must be some generic support for enums
ofNat n =
  case n of
    0  -> Black
    1  -> Blue
    2  -> Red
    3  -> Green
    4  -> Yellow
    5  -> Grey
    6  -> Fuschia
    7  -> Orange
    8  -> Teal
    9  -> Brown
    10 -> ColorTrue
    _ -> error "Color.ofNat given n > 10"
-}
toNat (Color c) = c

colorTrue = Color 10

instance Show Color where
  show (Color c) = show c

-- TODO: enumCtxVals?
enumColorsCtx :: (Monad m, HasSynth1Context m Color) => SearchT m (Ex Color)
enumColorsCtx = choice "enumColorsCtx" [
  ("ctx",   synthCtx),
  ("noCtx", enumVals >>= \c -> Ex.map (\_ -> c) <$> getDummyEx)
  ]

-- TODO: clearly bad design!
-- This can override the Color instance since color is only a type-synonym!
instance (Monad m) => HasEnumVals m Color where
  enumVals = oneOf "Color.enumVals" $ flip map (List.range 10) $ \k -> (show k, Color k)


instance Default Color where
  def = blank
