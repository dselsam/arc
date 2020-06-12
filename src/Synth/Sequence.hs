-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Sequence where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Data.List as List
import qualified Util.List as List
import qualified Data.Map as Map
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Data.Set as Set
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Spec (Spec, SynthFn)
import qualified Synth.Spec as Spec
import Synth.Context
import Synth.EagerFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import Synth.LazyFeatures
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Spec.USpec (USpec(USpec))
import Synth.Spec.TSpec (TSpec(TSpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.Spec.USpec as USpec



-- TODO:
--   - `Foldable` instead of `[]`?
--   - `Ord a` instead of `Int`?
--   - note that we could take `a`s with int features, but we assume that int features may be arbitrarily expensive

synthInts2BoolsSpecialValueP :: (Monad m) => SynthFn m TSpec (Ex [Int]) [Bool]
synthInts2BoolsSpecialValueP spec = do
  let xss = Spec.ctx spec
  -- Caller's responsibility to add count features
  f <- oneOf "specialFunction" [("max", maximum), ("min", minimum)]
  let vs :: Ex Int = Ex.map f xss
  pure $ flip Ex.map (Ex.zip xss vs) $ \(xs, v) -> map (==v) xs

synthGroupSetBoolFeaturesP :: (Monad m, Ord a) => SynthFn m TSpec (Ex [Set a]) [Bool]
synthGroupSetBoolFeaturesP spec = do
  let xsss = Spec.ctx spec
  guesses <- choice "synthGroupSetBoolFeaturesP" [
    ("hasUniqueElem", flip Ex.mapM xsss $ \xss -> do
        let isxs = zip [1..] xss
        pure $ flip map isxs $ \(i0, xs0) -> flip any xs0 $ \x0 ->
          not . flip any isxs $ \(i1, xs1) -> i0 /= i1 && Set.member x0 xs1),
    ("notContainedInOther", flip Ex.mapM xsss $ \xss -> do
        let isxs = zip [1..] xss
        pure $ flip map isxs $ \(i0, xs0) -> flip all isxs $ \(i1, xs1) ->
          i0 == i1 || not (Set.isSubsetOf xs0 xs1))
    ]
  guard $ Spec.check spec guesses -- TODO: annoying, this will always be used with the trivial spec
  pure guesses

synthSpecial :: (Monad m, Eq a, Ord a) => SynthFn m USpec (Ex [Bool], Ex [a]) a
synthSpecial spec@(USpec info (bs, xs)) = flip Ex.mapM (Ex.zip bs xs) $ \(bs, xs) ->
  liftO . List.getUnique id . map snd . filter fst $ zip bs xs

synthPermutation :: (Monad m, MonadIO m) => SynthFn m ESpec (Ex [Int]) [Int]
synthPermutation spec@(ESpec _ inputs labels) = do
  guard $ Ex.all List.allDistinct inputs
  guard $ all isPerm labels
  let ranks :: Ex [Int] = Ex.map List.indexInSorted inputs
  guard $ Ex.train ranks == labels
  pure ranks
  where
    isPerm :: [Int] -> Bool
    isPerm xs = List.sort xs == List.range (length xs)
