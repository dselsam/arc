-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Search.Options where

import Search.History
import Search.ScoreFn
import Search.Guess

data Options = Options {
  maxGuesses :: Int
  } deriving (Eq, Show, Ord)
