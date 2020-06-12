-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StrictData #-}
module Synth.Context where

import Synth.Basic
import Util.Imports
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Synth.ExInfo
import Search.SearchT
import Synth.ExInfo

class SynthContext ctx where
  partitionOn :: Ex Bool -> ctx -> (ctx, ctx)

instance SynthContext () where
  partitionOn _ _ = ((), ())

instance SynthContext (Ex a) where
  partitionOn = Ex.partitionOn

instance (SynthContext ctx1, SynthContext ctx2) => SynthContext (ctx1, ctx2) where
  partitionOn bs (ctx1, ctx2) =
    let (ctx1t, ctx1f) = partitionOn bs ctx1
        (ctx2t, ctx2f) = partitionOn bs ctx2
    in
      ((ctx1t, ctx2t), (ctx1f, ctx2f))

class SynthContextFlatten ctx1 ctx2 where
  flattenCtx :: ctx1 -> ctx2

instance SynthContextFlatten () () where
  flattenCtx _ = ()

instance SynthContextFlatten (Ex [a]) (Ex a) where
  flattenCtx ex = fst (Ex.flatten ex)

instance (SynthContextFlatten ctx1a ctx1b, SynthContextFlatten ctx2a ctx2b) => SynthContextFlatten (ctx1a, ctx2a) (ctx1b, ctx2b) where
  flattenCtx (ctx1a, ctx2a) = (flattenCtx ctx1a, flattenCtx ctx2a)

class SynthContextSelect ctx1 ctx2 where
  selectCtx :: Ex [Bool] -> ctx1 -> Maybe ctx2

instance SynthContextSelect () () where
  selectCtx _ _ = Just ()

instance (Eq a, Ord a) => SynthContextSelect (Ex [a]) (Ex a) where
  selectCtx bs xs = flip Ex.mapM (Ex.zip bs xs) $ \(bs, xs) ->
        List.getUnique id $ map snd . filter fst $ zip bs xs

instance (SynthContextSelect ctx1a ctx1b, SynthContextSelect ctx2a ctx2b) => SynthContextSelect (ctx1a, ctx2a) (ctx1b, ctx2b) where
  selectCtx bs (ctx1a, ctx2a) = do
    ctx1b <- selectCtx bs ctx1a
    ctx2b <- selectCtx bs ctx2a
    pure $ (ctx1b, ctx2b)
