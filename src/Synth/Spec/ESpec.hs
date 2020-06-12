-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.Spec.ESpec where

import Util.Imports
import Search.SearchT
import Search.DFS
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import Synth.ExInfo
import qualified Synth.Ex as Ex
import Synth.Spec
import Synth.Context
import qualified Util.List as List
import qualified Synth.ExInfo as ExInfo
import qualified Synth.Context as Context

data ESpec ctx a = ESpec {
  info   :: ExInfo,
  ctx    :: ctx,
  labels :: ForTrain a
  } deriving (Eq, Ord, Show)

instance (Eq a) => Spec ESpec ctx a where
  info  (ESpec info   _      _     )         = info
  ctx   (ESpec _      inputs _     )         = inputs
  check (ESpec _      _      labels) guesses = labels == Ex.train guesses
