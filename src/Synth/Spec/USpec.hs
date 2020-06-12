-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.Spec.USpec where

import Util.Imports
import Search.SearchT
import Search.DFS
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import Synth.ExInfo
import qualified Synth.Ex as Ex
import Synth.Spec
import Synth.Context
import qualified Util.List as List
import qualified Synth.Context as Context

data USpec ctx a = USpec {
  info        :: ExInfo,
  ctx         :: ctx
  } deriving (Show)

instance (Eq a, Ord a) => Spec USpec ctx [a] where
  info  (USpec info   _     )         = info
  ctx   (USpec _      inputs)         = inputs
  check (USpec _      _     ) guesses = Ex.all ((==1) . List.countDistinct id) guesses
