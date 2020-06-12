-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
module Util.Map where

import Util.Imports
import qualified Util.Int as Int
import qualified Data.Map as Map
import qualified Util.List as List

iter :: Map a b -> c -> (c -> a -> b -> c) -> c
iter m init f = Map.foldlWithKey' f init m

iterM :: (Monad m) => Map a b -> c -> (c -> a -> b -> m c) -> m c
iterM d start f = List.iterM (Map.assocs d) start (\c -> uncurry $ f c)

glueMaps :: Ord a => Eq b => [Map a b] -> Maybe (Map a b)
glueMaps maps = List.iterM maps Map.empty $ \acc map -> do
  iterM map acc $ \acc k v ->
    case Map.lookup k acc of
      Nothing -> pure $ Map.insert k v acc
      (Just v') -> guard (v == v') *> pure acc
