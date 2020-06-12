-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses, AllowAmbiguousTypes, FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Basic where

import Search.SearchT
import Util.List (range)
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Search.ScoreFn
import Search.DFS
import Search.Guess (Guess(Guess))
import qualified Search.Options
import qualified Search.Guess as Guess

find1E :: (Monad m) => String -> SearchT m (Ex a) -> SearchT m (ForTest a)
find1E s psi = do
  outputs <- find1 s psi
  pure $ Ex.test outputs

enumIntRange :: (Monad m) => Int -> SearchT m Int
enumIntRange n = oneOf "enumIntRange" $ flip map (range n) $ \k -> (show k, k)
