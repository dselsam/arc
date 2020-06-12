-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StrictData #-}
module Solver.ArcContext where

import qualified Synth.Ex as Ex
import Synth.Ex (Ex)
import Lib.Color
import Search.SearchT
import Synth.ExInfo
import Synth.EagerFeatures
import Synth.Context

data ArcContext = ArcContext {
  ints   :: EagerFeatures Int,
  colors :: EagerFeatures Color
  } deriving (Eq, Ord, Show)

instance SynthContext ArcContext where
  partitionOn mask (ArcContext intFeatures colorFeatures) =
    ((ArcContext (EagerFeatures intFeatures1) (EagerFeatures colorFeatures1)), (ArcContext (EagerFeatures intFeatures2) (EagerFeatures colorFeatures2)))

    where
      pOn (name, x) = let (left,right) = Ex.partitionOn mask x in
        ((name ++ "True", left), (name ++ "False", right))
      (intFeatures1, intFeatures2) =
        Prelude.unzip $ flip Prelude.map (choices intFeatures) $ pOn
      (colorFeatures1, colorFeatures2) =
        Prelude.unzip $ flip Prelude.map (choices colorFeatures) $ pOn
