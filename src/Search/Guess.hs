-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
module Search.Guess where

import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Search.Entry
import Search.History

data Guess a = Guess {
  value      :: a,
  history    :: History,
  nVisited   :: Int,
  nFailed    :: Int
  } deriving (Eq, Ord, Show, Generic, Generic1)

instance NFData a => NFData (Guess a)
