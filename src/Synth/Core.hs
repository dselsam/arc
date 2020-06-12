-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
module Synth.Core where

import Synth.Basic
import Util.Imports
import Util.List (range)
import qualified Util.List as List
import qualified Util.Map as Map
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Synth.Ex as Ex
import Search.SearchT
import Synth.Spec (Spec, SynthFn)
import qualified Synth.Spec as Spec
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec.ESpec as ESpec
import qualified Synth.Context as Context
import Synth.EagerFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import Debug.Trace

eqConstE :: (Monad m, Eq a) => SynthFn m ESpec (Ex a) Bool
eqConstE (ESpec _ inputs labels) = do
  let trues  = map fst . filter snd $ zip (Ex.train inputs) labels
  let falses = map fst . filter (not . snd) $ zip (Ex.train inputs) labels
  guard . not . null   $ trues
  guard . List.allSame $ trues
  let special = head trues
  guard . not $ special `elem` falses
  pure $ Ex.map (==special) inputs

identityP :: (Monad m, Spec spec (Ex a) a, Eq a, Show a) => SynthFn m spec (Ex a) a
identityP spec = do
  let x = Spec.ctx spec
  guard $ Spec.check spec x
  pure x

constValueE :: (Monad m, Show b, Eq b) => SynthFn m ESpec ctx b
constValueE spec = do
  let labels = ESpec.labels spec
  guard . not . null $ labels
  guard . List.allSame $ labels
  let guess = head labels
  guess <- oneOf "constValueE" [(show guess, guess)]
  pure $ Ex.replicate (Spec.info spec) guess

lookupTableE :: (Monad m, Show a, Show b, Ord a, Eq b, Ord b) => SynthFn m ESpec (Ex a) b
lookupTableE spec@(ESpec _ inputs labels) = do
  lookupTableWithCounts :: Map a (b, Int) <- List.iterM (zip (Ex.train inputs) labels) Map.empty $ \acc (k, v) ->
    case Map.lookup k acc of
      Nothing      -> pure $ Map.insert k (v, 1) acc
      Just (v', n) -> do
        guard (v == v')
        pure $ Map.insert k (v, n+1) acc

  guard . (>=2) . length . filter (\(v, c) -> c >= 2) . Map.elems $ lookupTableWithCounts
  guard . List.allDistinct . map fst . Map.elems $ lookupTableWithCounts
  let lookupTable :: Map a b = Map.map fst lookupTableWithCounts
  lookupTable <- oneOf "lookupTableE" [(show lookupTable, lookupTable)]
  liftO $ Ex.mapM (flip Map.lookup lookupTable) inputs

tryIfEq :: (Monad m, Eq a, Eq b, Ord b, Show b) => SynthFn m ESpec (Ex a) b
tryIfEq (ESpec info inputs labels) = do
  let ys = Set.fromList labels
  guard $ Set.size ys == 2
  let y1 = Set.elemAt 0 ys
  let y2 = Set.elemAt 1 ys
  (label2bool, bool2label) <- choice "label2bool" [
    (show y1, pure ((==y1), (\b -> if b then y1 else y2))),
    (show y2, pure ((==y2), (\b -> if b then y2 else y1)))
    ]
  Ex.map bool2label <$> eqConstE (ESpec info inputs (map label2bool labels))

synthBasecase :: (Monad m, Eq a, Ord a, Show a) => SynthFn m ESpec (Ex a) a
synthBasecase spec = choice "synthBasecase"
  [("identityP", identityP spec),
   ("constValueE", constValueE spec),
   ("lookupTableE", lookupTableE spec)]

focusing :: (Monad m) => SynthFn m ESpec (Ex a) b -> SynthFn m ESpec (EagerFeatures a) b
focusing synthEx (ESpec info (EagerFeatures xs) labels) = do
  x <- oneOf "focus" xs
  synthEx $ ESpec info x labels


-- TODO: Not thrilled about "reconstructing" the original structure...
--   - but it has been so convenient to "forget" the nested list structure
synthSwaps :: (Monad m, MonadIO m, Eq a, Ord a, Show a) => SynthFn m ESpec (Ex a, Ex Int) a
synthSwaps (ESpec info (inputs, idxs) labels) = do
  unless (length (Ex.train inputs) == length (Ex.train idxs)) $
    liftIO . traceIO $ "[synthSwaps] BAD"

  trainMaps :: Map Int (Map a a) <- List.iterM (zip3 (Ex.train inputs) (Ex.train idxs) labels) Map.empty $ \acc (input, idx, label) -> do
    let map = Map.findWithDefault Map.empty idx acc
    case Map.lookup input map of
      Nothing -> pure $ Map.insert idx (Map.insert input label map) acc
      Just x  -> do
        guard $ x == label
        pure acc

  guard $ all isSwap (Map.elems trainMaps)

  let testVals :: Map Int (Set a) = List.iter (zip (Ex.test inputs) (Ex.test idxs)) Map.empty $ \acc (input, idx) -> pure $
        Map.insertWith Set.union idx (Set.fromList [input]) acc

  guard $ all ((==2) . Set.size) (Map.elems testVals)

  let testGuesses :: ForTest a = flip map (zip (Ex.test inputs) (Ex.test idxs)) $ \(input, idx) ->
        let Just vals = Map.lookup idx testVals in
          if input == Set.elemAt 0 vals then Set.elemAt 1 vals else Set.elemAt 0 vals

  pure $ Ex labels testGuesses

  where
    isSwap :: (Eq a, Ord a) => Map a a -> Bool
    isSwap m =
      let keys  = Map.keys m
          elems = Map.elems m
      in
        length keys == 2
        && List.countDistinct id elems == 2
        && case (keys, elems) of
             ([x1, x2], [y1, y2]) -> (x1, x2) `elem` [(y1, y2), (y2, y1)]
