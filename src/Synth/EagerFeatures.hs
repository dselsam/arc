-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
module Synth.EagerFeatures where

import Synth.Basic
import Util.Imports
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Context

newtype EagerFeatures a = EagerFeatures {
  choices :: [Choice (Ex a)]
  } deriving (Eq, Ord, Show)

instance SynthContext (EagerFeatures a) where
  partitionOn bs (EagerFeatures choices) =
    let bothChoices :: [Choice (Ex a, Ex a)] = map (\(name, ex) -> (name, Ex.partitionOn bs ex)) choices in
      (EagerFeatures $ map (\(name, (ex1, _)) -> (name, ex1)) bothChoices,
       EagerFeatures $ map (\(name, (_, ex2)) -> (name, ex2)) bothChoices)

instance SynthContextFlatten (EagerFeatures [a]) (EagerFeatures a) where
  flattenCtx (EagerFeatures choices) = EagerFeatures $ flip map choices $ \(n, ex) -> (n, fst (Ex.flatten ex))

instance (Eq a, Ord a) => SynthContextSelect (EagerFeatures [a]) (EagerFeatures a) where
  selectCtx bs (EagerFeatures choices) = do
    let keeps = flip concatMap choices $ \(n, xs) ->
          case selectCtx bs xs of
            Nothing -> []
            Just x -> [(n, x)]
    pure $ EagerFeatures keeps

append :: EagerFeatures a -> [Choice (Ex a)] -> EagerFeatures a
append efs cs = EagerFeatures (choices efs ++ cs)

prepend :: EagerFeatures a -> [Choice (Ex a)] -> EagerFeatures a
prepend efs cs = EagerFeatures (cs ++ choices efs)
