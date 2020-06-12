-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleInstances #-}
module Lib.Blank where

import Util.Imports
import Data.Default

class (Eq a) => HasBlank a where
  blank :: a

isBlank :: (HasBlank a) => a -> Bool
isBlank x = x == blank

nonBlank :: (HasBlank a) => a -> Bool
nonBlank x = not . isBlank $ x

orD   d x y = if nonBlank x || nonBlank y  then d else blank
andD  d x y = if nonBlank x && nonBlank y  then d else blank

norD  d x y = if nonBlank x || nonBlank y  then blank else d
nandD d x y = if nonBlank x && nonBlank y  then blank else d

xorD   d x y = if xor (nonBlank x) (nonBlank y) then d else blank
nxorD  d x y = if xor (nonBlank x) (nonBlank y) then blank else d

notD   d x   = if nonBlank x then blank else d

or x y = if nonBlank x then x else y

-- Instances
eqOrBlanks x y
  | x == y = True
  | isBlank x || isBlank y = True
  | otherwise = False

eqOrBlank2 x y
  | x == y = True
  | isBlank y = True
  | otherwise = False

instance HasBlank Int where
  blank = 0

instance HasBlank Bool where
  blank = False
