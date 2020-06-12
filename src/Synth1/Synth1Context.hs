-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Synth1.Synth1Context where

import Synth.Ex
import Synth.ExInfo (ExInfo(ExInfo))
import qualified Synth.ExInfo as ExInfo
import qualified Synth.Ex as Ex
import Search.SearchT
import qualified Data.List as List

class (Monad m) => HasTrainTest m where
  getNumTrain :: SearchT m Int
  getNumTest  :: SearchT m Int
  getDummyEx :: SearchT m (Ex ())
  getDummyEx = do
    nTrain <- getNumTrain
    nTest <- getNumTest
    pure $ Ex.replicate (ExInfo nTrain nTest) ()

class (HasTrainTest m) => HasSynth1Context m a where
  synthCtx :: SearchT m (Ex a)
  synthCtx = deadend "nothing in context"
