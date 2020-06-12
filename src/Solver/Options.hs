-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Options where

data Options = Options {
  timeoutSeconds :: Int,
  maxGuesses     :: Int,
  schedule       :: [Int]
  } deriving (Eq, Ord, Show)
