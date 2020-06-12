-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.Spec.DSpec where

import Util.Imports
import Search.SearchT
import Search.DFS
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import Synth.ExInfo
import qualified Synth.Ex as Ex
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Spec
import qualified Data.List as List

data DSpec ctx a = DSpec {
  info   :: ExInfo,
  ctx    :: ctx,
  labels :: ForTrain [a]
  } deriving (Eq, Ord, Show)

instance (Eq a) => Spec DSpec ctx a where
  info   (DSpec info      _   _     )      = info
  ctx    (DSpec _         ctx _     )      = ctx
  check  (DSpec _      _   labels) guesses = flip all (zip labels (Ex.train guesses)) $ \(label, guess) -> guess `elem` label

nExactSpecs :: DSpec ctx a -> Int
nExactSpecs (DSpec _ _ labels) = List.product (map length labels)

blast :: (Monad m) => DSpec ctx a -> SearchT m (ESpec ctx a)
blast (DSpec info ctx labels) = do
  labels :: ForTrain a <- flip mapM (zip [1..] labels) $ \(i, labels) ->
    oneOf ("D" ++ show i) $ flip map (zip [1..] labels) $ \(j, label) -> (show j, label)
  pure $ ESpec info ctx labels
