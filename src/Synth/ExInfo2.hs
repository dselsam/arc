-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.ExInfo2 where

import Synth.ExInfo
import Synth.Ex

partitionOn :: Ex Bool -> (ExInfo, ExInfo)
partitionOn bs = (ExInfo (length $ filter id (train bs))  (length $ filter id (test bs)),
                  ExInfo (length $ filter not (train bs)) (length $ filter not (test bs)))
