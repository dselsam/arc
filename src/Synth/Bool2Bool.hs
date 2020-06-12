-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Bool2Bool where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Data.Set as Set
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Spec (Spec, SynthFn)
import qualified Synth.Spec as Spec
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Bool
import Synth.Core
import Synth.Context

-- TODO: synthBools2Bool that considers conjunctions??
synthBool2BoolE :: (Monad m) => SynthFn m ESpec (Ex Bool) Bool
synthBool2BoolE spec@(ESpec _ inputs _) = choice "synthBool2BoolE" [
  -- Note that eqConstE handles negation for bools automatically
  ("eq", eqConstE spec)
  ]
