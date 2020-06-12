-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.Spec where

import Util.Imports
import Search.SearchT
import Search.DFS
import Synth.ExInfo (ExInfo(ExInfo))
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex

type ReconstructFn a b = Ex a -> Maybe (Ex b)
type SynthFn  m spec ctx a = spec ctx a -> SearchT m (Ex a)
type SynthFn1 m s1 c1 a1 s2 c2 a2 = s1 c1 a1 -> SearchT m (s2 c2 a2, ReconstructFn a2 a1)

class Spec spec ctx a where
  info  :: spec ctx a -> ExInfo
  ctx   :: spec ctx a -> ctx
  check :: spec ctx a -> Ex a -> Bool
