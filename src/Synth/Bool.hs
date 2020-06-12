-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Bool (DListOptions(DListOptions), decisionList, decisionListID, ltConstE, strictOpts, relaxedOpts, initialFuel) where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Util.List as List
import qualified Data.List as List
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import Synth.ExInfo as ExInfo
import Synth.ExInfo2 as ExInfo
import qualified Data.Set as Set
import qualified Synth.Ex as Ex
import Search.SearchT
import Search.DFS
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import Synth.EagerFeatures
import qualified Synth.Context as Context
import Synth.Context
import Synth.Spec
import qualified Synth.Spec as Spec
import Synth.Spec.ESpec
import qualified Synth.Spec.ESpec as ESpec


-- TODO: bool specs?

ltConstE :: (Monad m, Ord a) => SynthFn m ESpec (Ex a) Bool
ltConstE spec = deadend "NYI"

data DListOptions = DListOptions {
  initialFuel       :: Int,
  minTrueTrain      :: Int,
  minTrueTest       :: Int,
  testFalseRequired :: Bool
  } deriving (Eq, Ord, Show)

strictOpts  fuel = DListOptions fuel 2 1 True
relaxedOpts fuel = DListOptions fuel 1 1 False

decisionList :: (Monad m, MonadIO m, SynthContext ctx, Show b) => DListOptions -> SynthFn m ESpec ctx b -> SynthFn m ESpec (EagerFeatures Bool, ctx) b
decisionList opts synthLeafE spec = decisionListCore (initialFuel opts) opts synthLeafE spec

decisionListID :: (Monad m, MonadIO m, SynthContext ctx, Show b) => [Int] -> SynthFn m ESpec ctx b -> SynthFn m ESpec (EagerFeatures Bool, ctx) b
decisionListID schedule synthLeafE spec = choice "dlistDepth" $ map (\d -> (show d, decisionList (strictOpts d) synthLeafE spec)) schedule

decisionListCore :: (Monad m, MonadIO m, SynthContext ctx, Show b) => Int -> DListOptions -> SynthFn m ESpec ctx b -> SynthFn m ESpec (EagerFeatures Bool, ctx) b
decisionListCore fuel opts synthLeafE spec
  | fuel == 0 = basecase spec
  | otherwise = core fuel spec

  where
    basecase (ESpec info (_, ctx) labels) = choice "DList[basecase]" [
      ("empty", do
          guard $ ExInfo.nTrain info == 0 && ExInfo.nTest info == 0
          pure $ Ex [] []),
      ("leaf", synthLeafE $ spec { ESpec.ctx = ctx })
      ]

    core fuel spec@(ESpec info (bs, ctx) labels) = choice ("DList[" ++ show fuel ++ "]") [
      ("baseline", basecase spec),
      ("ite", do
          (rank, name, nLeft, b, trueGuesses, maybeFalseGuesses, bsFalse, infoFalse, ctxFalse, labelsFalse) <- findBestsOnK ("DList[" ++ show fuel ++ "]") scoreFns $ do
            (rank, name, b) :: (Int, String, Ex Bool) <- oneOfX "decisionListE" $ EagerFeatures.choices bs
            unless (length (Ex.train b) == length labels) $ do
              traceM $ "[decisionListE] ERROR " ++ show (length (Ex.train b), length labels)

            let (bsTrue, bsFalse) = Ex.partitionOn b b

            guard $ length (Ex.train bsTrue)  >= minTrueTrain opts -- Note that this is aggressive
            guard $ length (Ex.test  bsTrue)  >= minTrueTest opts

            guard $ (null (Ex.train bsFalse)) <= (null (Ex.test bsFalse))
            when (testFalseRequired opts) $ guard $ (null (Ex.train bsFalse)) == (null (Ex.test bsFalse))

            let (infoTrue, infoFalse)     = ExInfo.partitionOn b
            let (ctxTrue, _)              = Context.partitionOn b ctx
            let (_, bsFalse)              = Context.partitionOn b bs
            let (_, ctxFalse)             = Context.partitionOn b ctx
            let (labelsTrue, labelsFalse) = List.partitionOn (Ex.train b) labels

            -- liftIO . traceIO $ "[DLIST] TRY[" ++ show fuel ++ ", " ++ show rank ++ "]: " ++ show name
            trueGuesses       <- find1 "true" . synthLeafE $ ESpec infoTrue ctxTrue labelsTrue
            maybeFalseGuesses <- find1O "falseLookahead" . synthLeafE $ ESpec infoFalse ctxFalse labelsFalse
            pure $ (rank, name, ExInfo.nTrain infoFalse + ExInfo.nTest infoFalse, b, trueGuesses, maybeFalseGuesses, bsFalse, infoFalse, ctxFalse, labelsFalse)

          -- liftIO . traceIO $ "[DLIST] FIRE[" ++ show fuel ++ ", " ++ show rank ++ "]: " ++ show name
          -- liftIO . traceIO $ "[DLIST] LABELS: " ++ show labelsFalse
          falseGuesses <- case maybeFalseGuesses of
            Just falseGuesses -> pure falseGuesses
            Nothing -> decisionListCore (fuel-1) opts synthLeafE $ ESpec infoFalse (bsFalse, ctxFalse) labelsFalse
          pure $ Ex.unpartitionOn b trueGuesses falseGuesses)
      ]

    -- TODO: play with this
    -- TODO: if this is literally the scoreFn always, we don't need to try them all!
    -- TODO: take a few for each function?
    -- TODO: take a list of lists of bool features?
    -- TODO: diversity?
    scoreFns = [
      ("rank",  \(rank, name, nLeft, _, _, maybeFalseGuesses, _, _, _, _) ->
          case maybeFalseGuesses of
            Nothing -> (rank, 0)
            Just _  -> (-1, rank)),
      ("nLeft", \(rank, name, nLeft, _, _, maybeFalseGuesses, _, _, _, _) ->
          case maybeFalseGuesses of
            Nothing -> (nLeft, rank)
            Just _  -> (-1, rank))
      ]
