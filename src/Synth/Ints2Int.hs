-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Ints2Int where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Util.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Data.Set as Set
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Spec (Spec, SynthFn, SynthFn1)
import qualified Synth.Spec as Spec
import qualified Synth.Spec.ESpec as ESpec
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Context
import Synth.EagerFeatures
import qualified Synth.EagerFeatures as EagerFeatures
--import Synth.Bool
import Synth.Core

import Debug.Trace

-- TODO: have synthInts2IntE take options
data SynthInts2IntOptions = SynthInts2IntOptions {
  maxConstantAbs :: Int,
  initialFuel    :: Int
  } deriving (Eq, Ord, Show)

defaultSynthInts2IntOptions :: SynthInts2IntOptions
defaultSynthInts2IntOptions = SynthInts2IntOptions { maxConstantAbs = 8, initialFuel = 1 }

-- TODO: notice that the 1 is hardcoded for now.
synthInts2IntE :: (Monad m) => SynthFn m ESpec (EagerFeatures Int) Int
synthInts2IntE spec@(ESpec _ xs labels) = synthIntE (initialFuel defaultSynthInts2IntOptions) spec
  where
    synthIntE 0    spec = basecase 0 spec
    synthIntE fuel spec = choice "synthIntE" [
      ("basecase", basecase fuel spec),
      ("backup",   do
          x <- oneOf "arg" $ EagerFeatures.choices xs
          let specWithArg = spec { ESpec.ctx = (x, xs) }
          (newSpec, reconstruct) <- choice "backup" [
            ("add",  backupAddE  specWithArg),
            ("mul",  backupMulE  specWithArg),
            ("div1", backupDiv1E specWithArg),
            ("div2", backupDiv2E specWithArg)
            ]
            -- TODO: current spot!
          guesses <- synthIntE (fuel - 1) newSpec
          liftO $ reconstruct guesses)
      ]

    basecase fuel spec = choice "leaf" [
      ("idP",    do
          x <- oneOf "id" $ EagerFeatures.choices xs
          neg <- oneOf "neg" [("no", id), ("yes", \x -> -x)]
          identityP (spec { ESpec.ctx = (Ex.map neg x) })),
      ("constE", do
          x <- constValueE spec
          when (fuel < initialFuel defaultSynthInts2IntOptions) $
            guard $ Ex.all (\x -> abs x <= maxConstantAbs defaultSynthInts2IntOptions) x
          pure x)
      ]

backupAddE :: (Monad m) => SynthFn1 m ESpec (Ex Int, ctx) Int ESpec ctx Int
backupAddE spec@(ESpec info (xs, ctx) labels) = do
  -- y = x + ?k
  let newLabels :: ForTrain Int = map (\(x, y) -> y - x) (zip (Ex.train xs) labels)
  let reconstruct guesses = pure $ Ex.map (uncurry (+)) (Ex.zip xs guesses)
  pure (ESpec info ctx newLabels, reconstruct)

backupMulE :: (Monad m) => SynthFn1 m ESpec (Ex Int, ctx) Int ESpec ctx Int
backupMulE spec@(ESpec info (xs, ctx) labels) = do
  -- y = x * ?k
  newLabels :: ForTrain Int <- flip mapM (zip (Ex.train xs) labels) $ \(x, y) -> do
    guard $ x /= 0
    guard $ y `rem` x == 0
    pure $ y `div` x
  guard . all (/=0) $ Ex.test xs
  let reconstruct guesses = pure $ Ex.map (uncurry (*)) (Ex.zip xs guesses)
  pure (ESpec info ctx newLabels, reconstruct)

backupDiv1E :: (Monad m) => SynthFn1 m ESpec (Ex Int, ctx) Int ESpec ctx Int
backupDiv1E spec@(ESpec info (xs, ctx) labels) = do
  -- y = ?k / x
  newLabels :: ForTrain Int <- flip mapM (zip (Ex.train xs) labels) $ \(x, y) -> do
    guard $ x /= 0
    pure  $ x * y
  guard . all (/= 0) $ Ex.test xs
  let reconstruct guesses = pure $ Ex.map (uncurry div) (Ex.zip guesses xs)
  pure (ESpec info ctx newLabels, reconstruct)

backupDiv2E :: (Monad m) => SynthFn1 m ESpec (Ex Int, ctx) Int ESpec ctx Int
backupDiv2E spec@(ESpec info (xs, ctx) labels) = do
  -- y = x / ?k
  newLabels :: ForTrain Int <- flip mapM (zip (Ex.train xs) labels) $ \(x, y) -> do
    guard $ y /= 0
    guard $ x `rem` y == 0
    pure  $ x `div` y
  let reconstruct guesses = do { guard (Ex.all (/= 0) guesses); pure $ Ex.map (uncurry div) (Ex.zip xs guesses) }
  pure (ESpec info ctx newLabels, reconstruct)
