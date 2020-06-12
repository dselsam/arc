-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
module Util.LList where

data LList a = LList {
  size  :: Int,
  elems :: [a]
  } deriving (Eq, Ord, Show)

empty :: LList a
empty = LList 0 []

cons :: a -> LList a -> LList a
cons x (LList n xs) = LList (n+1) (x:xs)

toList :: LList a -> [a]
toList (LList _ xs) = xs
