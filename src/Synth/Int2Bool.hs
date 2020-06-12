-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Int2Bool where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Data.Set as Set
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Spec (Spec, SynthFn)
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec as Spec
import Synth.Bool
import Synth.Core

synthInt2BoolE :: (Monad m) => SynthFn m ESpec (Ex Int) Bool
synthInt2BoolE spec = choice "synthInt2BoolE" [
  -- We comment this out for now, and make it the caller's responsible to augment the Int features with the moduli
  ("modP", modEqP spec),
  ("eq",   eqConstE spec),
  ("lt",   ltConstE spec)
  ]

modEqP :: (Monad m, Spec spec (Ex Int) Bool) => SynthFn m spec (Ex Int) Bool
modEqP spec = do
  let x = Spec.ctx spec
  k  <- oneOf "modulus" [("2", 2), ("3", 3)]
  r  <- oneOf "remainder" $ map (\r -> (show r, r)) (List.range k)
  let y = Ex.map (\x -> x `mod` k == r) x
  guard $ Spec.check spec y
  pure y

synthInt2BoolP :: (Monad m, Spec spec (Ex Int) Bool) => SynthFn m spec (Ex Int) Bool
synthInt2BoolP spec = choice "synthInt2BoolP" [
  ("==small",    do
      k <- oneOf "small" [("0", 0), ("1", 1), ("2", 1)]
      pure $ Ex.map (==k) $ Spec.ctx spec),
  ("mod==small", modEqP spec)
  ]
