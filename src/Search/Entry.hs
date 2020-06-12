-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
module Search.Entry where

import Control.DeepSeq
import GHC.Generics (Generic, Generic1)

data Entry = Entry { choicePoint :: String, choice :: String } deriving (Eq, Ord, Generic)

instance NFData Entry

instance Show Entry where
  show (Entry cp c) = cp ++ "=" ++ c
