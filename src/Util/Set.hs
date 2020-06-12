-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
module Util.Set where

import Util.Imports
import qualified Util.Int as Int
import qualified Data.Set as Set
import qualified Util.List as List

iter :: Set a -> c -> (c -> a -> c) -> c
iter m init f = Set.foldl' f init m

iterM :: (Monad m) => Set a -> c -> (c -> a -> m c) -> m c
iterM d = List.iterM (Set.toList d)

intersectMany :: Ord a => [Set a] -> Set a
intersectMany []     = Set.empty
intersectMany [s]    = s
intersectMany (s:ss) = Set.intersection s (intersectMany ss)
