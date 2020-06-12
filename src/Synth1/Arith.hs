-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Synth1.Arith where

import Synth1.Basic
import Util.Imports
import Util.List
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Data.Ratio
import Search.SearchT
import Synth1.Synth1Context

synthIntsExactSpec :: (Monad m, HasSynth1Context m Int, HasEnumIntFeatures m a) => Ex a -> ForTrain Int -> SearchT m (ForTest Int)
synthIntsExactSpec inputs outputs = synthIntsExactSpecCore 2 inputs outputs
  where
    synthIntsExactSpecCore 0    inputs outputs = deadend ""
    synthIntsExactSpecCore fuel inputs outputs = choice "synthIntsExactSpec" [
      ("const", do
          guard $ allSame outputs
          pure $ map (\_ -> head outputs) (Ex.test inputs)),
      ("unary", do
          intInputs <- synthCtx
          choice "unary" [
            ("id", do
                guard $ all (\(intInput, output) -> intInput == output) (zip (Ex.train intInputs) outputs)
                pure $ Ex.test intInputs),
            ("mul", do
                -- output = input * k
                guard $ Ex.all (\intInput -> intInput /= 0) intInputs
                ksTrain <- liftO $ flip mapM (zip (Ex.train intInputs) outputs) $ \(intInput, output) -> do
                  guard $ output `rem` intInput == 0
                  pure  $ output `div` intInput
                ksTest <- synthIntsExactSpecCore (fuel-1) inputs ksTrain
                pure $ flip map (zip (Ex.test intInputs) ksTest) $ uncurry (*)),
            ("div", do
                -- output * k = input
                guard $ all (\output -> output /= 0) outputs
                ksTrain <- liftO $ flip mapM (zip (Ex.train intInputs) outputs) $ \(intInput, output) -> do
                  guard $ intInput `rem` output == 0
                  pure  $ intInput `div` output
                guard $ all (\k -> k /= 0) ksTrain
                ksTest <- synthIntsExactSpecCore (fuel-1) inputs ksTrain
                guard $ all (\k -> k /= 0) ksTest
                pure $ flip map (zip (Ex.test intInputs) ksTest) $ uncurry div),
            ("add", do
                -- input + k = output
                ksTrain <- liftO $ flip mapM (zip (Ex.train intInputs) outputs) $ \(intInput, output) -> do
                  pure $ output - intInput
                ksTest <- synthIntsExactSpecCore (fuel-1) inputs ksTrain
                pure $ flip map (zip (Ex.test intInputs) ksTest) $ uncurry (+))
            ])
      ]
