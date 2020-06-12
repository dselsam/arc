-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.LazyFeatures where

import Synth.Basic
import Util.Imports
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Search.SearchT

newtype LazyFeatures m a = LazyFeatures {
  choose :: SearchT m (Ex a)
  }

class HasBasicLazyFeatures m a b where
  getBasicLazyFeatures :: Ex a -> LazyFeatures m b
