-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
module Util.Pair where

import Util.Imports
import qualified Util.Int as Int
import qualified Data.Set as Set

map :: (a -> b) -> (a, a) -> (b, b)
map f (a1, a2) = (f a1, f a2)
