-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses, AllowAmbiguousTypes, FlexibleInstances, ScopedTypeVariables, FlexibleContexts #-}
module Synth1.Basic where

import Synth1.Synth1Context
import Util.Imports
import Util.List (range, count)
import qualified Util.List as List
import qualified Data.List as List
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import qualified Data.Set as Set
import qualified Data.Map as Map
import Search.SearchT
import Search.DFS (enumAll)
import Data.List (sortOn)
import Debug.Trace

class (Monad m) => HasEnumVals m a where
  enumVals :: SearchT m a

class (Monad m) => HasEnumBoolFeatures m a where
  enumBoolFeatures :: SearchT m (a -> Bool)

class (Monad m) => HasEnumIntFeatures m a where
  enumIntFeatures :: SearchT m (a -> Int)

class (Monad m) => HasEnumReduceFeatures m c a where
  -- TODO: constant design struggle, where to put the Ex
  -- To support "optional" features, we either need to explicitly return options,
  -- or else take the Ex as an argument outside of the SearchT return type.
  -- On the other hand, there are examples where we want the flexibility of
  -- returning functions that are associated with particular examples but that
  -- can be applied to many different arguments.
  -- For now we sacrifice the ability to have optional arguments, to keep things uniform,
  -- but we will revisit in the future.
  -- Could we make the type `SearchT m (Ex (c a -> SearchT m a))`?
  enumReduceFeatures :: SearchT m (Ex (c a -> a))

class (Monad m) => HasEnumUnaryOps m a where
  enumUnaryOps :: SearchT m (Ex (a -> a))

-- TODO: it is convenient to have `Ex` datastructures with the functions
-- so we can jointly map over the inputs and these functions (possibly applying them multiple times within a function)
class (Monad m) => HasEnumBinOps m a where
  enumBinOps :: SearchT m (Ex (a -> a -> a))

class (Monad m) => HasReduceBinOps m c a where
  enumReduceBinOps :: SearchT m ((a -> a -> a) -> c a -> a)

class (Monad m) => HasEnumBinPreds m a where
  enumBinPreds :: SearchT m (a -> a -> Bool)

enumIntRange :: (Monad m) => Int -> SearchT m Int
enumIntRange n = oneOf "enumIntRange" $ flip map (range n) $ \k -> (show k, k)

enumListElems :: (Monad m, Show a) => [a] -> SearchT m a
enumListElems xs = oneOf "enumListElems" $ map (\x -> (show x, x)) xs

{-
-- TODO: this should be lazy! but is eager!
--   - Commenting out because there are perf/semantic tradeoffs between different implementations
--     of unique.
enumUniq :: (Monad m, Eq a, Ord a) => SearchT m a -> SearchT m a
enumUniq f = do
  xs <- lift $ enumAll f
  enumListElems $ List.uniq xs
-}

enumIntBoolFeatures :: (Monad m, HasEnumIntFeatures m a) => SearchT m (a -> Bool)
enumIntBoolFeatures = do
  int2bool <- choice "enumIntBoolFeatures" [
    -- TODO: more! backwards support!
    ("eq",     do
        k <- enumListElems [0, 1, 2, 3, 4, 5, 6, 7]
        pure (==k)),
    ("gt",     do
        k <- enumListElems [0, 1]
        pure (>k)),
    ("parity", do
        k <- enumListElems [0, 1]
        pure $ \n -> mod n 2 == k)
    ]
  phi2int <- enumIntFeatures
  pure $ int2bool . phi2int

-- TODO: uncanny typeclass valley, problematic design
enumGroupIntBoolFeatures :: (Monad m, HasEnumIntFeatures m a, Eq a, Ord a) => SearchT m ([a] -> [Bool])
enumGroupIntBoolFeatures = do
  -- factor THIS out
  phi2ints <- choice "enumGroupIntBoolFeatures.toInts" [
    ("independent", map <$> enumIntFeatures),
    ("counts",      pure List.counts)
    ]
  -- TODO: generalize!
  choice "enumGroupIntBoolFeatures" [
    ("max", do
        pure $ \xs -> let y = maximum (phi2ints xs) in
          map (\x -> x > 0 && x == y) (phi2ints xs)),
    ("min", do
        pure $ \xs -> let y = minimum (phi2ints xs) in
          map (==y) (phi2ints xs)),
    ("distinct", pure $ \xs ->
        let ks = phi2ints xs in
          map (\k -> count (==k) ks == 1) ks)
    ]

-- TODO: duplication with the int features
enumCountFeatures :: (Monad m, Eq b, Ord b) => SearchT m (a -> b) -> SearchT m ([a] -> [Bool])
enumCountFeatures phi2psis = do
  phi2psi <- phi2psis
  let cnts = List.counts . map phi2psi
  choice "countFeatures" [
    ("max", pure $ \xs -> let y = maximum (cnts xs) in
        map (\x -> x > 0 && x == y) (cnts xs)),
    ("min", pure $ \xs -> let y = minimum (cnts xs) in
        map (==y) (cnts xs)),
    ("distinct", pure $ \xs -> let ks = cnts xs in
        map (\k -> count (==k) ks == 1) ks)
    ]

enumGroupSetBoolFeatures :: (Monad m, Eq a, Ord b) => SearchT m (a -> Set b) -> SearchT m ([a] -> [Bool])
enumGroupSetBoolFeatures phi2sets = do
  phi2set <- phi2sets
  choice "enumGroupSetBoolFeatures" [
    -- TODO: can we compute `xsys` in only one place? We would need to sample all the entropy before the \xs
    ("hasUniqueElem", pure $ \xs ->
        let isxsys = zip3 [1..] xs (map phi2set xs)
            hasUnique (i0, x0, ys0) = flip any ys0 $ \y0 ->
              not . flip any isxsys $ \(i1, x1, ys1) -> i0 /= i1 && Set.member y0 ys1
        in
          map hasUnique isxsys),
    ("notContainedInOther", pure $ \xs ->
        let xsys = zip xs (map phi2set xs)
            notContainedInOther (x0, ys0) = flip all xsys $ \(x1, ys1) -> x0 == x1 || not (Set.isSubsetOf (phi2set x0) (phi2set x1))
        in
          map notContainedInOther xsys)
    ]

enumAllGroupBoolFeatures :: (Monad m, Eq a, Ord a, Ord b, HasEnumBoolFeatures m a, HasEnumIntFeatures m a) => SearchT m (a -> Set b) -> SearchT m ([a] -> [Bool])
enumAllGroupBoolFeatures phi2sets = do
  phi <- choice "enumAllGroupBoolFeatures" [
    ("allTrue",        do { pure $ map (\_ -> True) }),
    ("2bool",          do { phi2bool <- enumBoolFeatures; pure $ \xs -> Prelude.map phi2bool xs }),
    ("group2int2bool", enumGroupIntBoolFeatures),
    ("group2set2bool", enumGroupSetBoolFeatures phi2sets),
    -- TODO: restore more fine-grained ranking
    ("2int2bool",      do { phi2int2bool <- enumIntBoolFeatures; pure $ \xs -> Prelude.map phi2int2bool xs })
    ]
  neg <- choice "negate" [("no", pure id), ("yes", pure not)]
  pure $ map neg . phi


-- TODO: make the set argument a list?
enumGroupSetValueMaps :: (Monad m, Eq a, Ord b) => SearchT m (a -> Set b) -> [a] -> SearchT m [b]
enumGroupSetValueMaps phi2sets inputs = do
  sets :: [Set b] <- flip map inputs <$> phi2sets
  choice "enumGroupSetValueMaps" [
    ("singletons", do
        guard $ all (\set -> Set.size set == 1) sets
        pure $ map (head . Set.toList) sets),
    ("uniques", do
        let iSets :: [(Integer, Set b)] = zip [1..] sets
        liftO $ flip mapM iSets $ \(i1, xs1) ->
          flip List.first (Set.toList xs1) $ \(x1 :: b) -> do
            guard $ not $ flip any iSets $ \(i2, xs2) ->
              i1 /= i2 && Set.member x1 xs2
            pure x1)
    ]

-- Extend with group support?
enumListValueMaps :: (Monad m, Eq a, Ord b) => b -> SearchT m (a -> [b]) -> SearchT m (a -> b)
enumListValueMaps dflt phi2lists = do
  phi2list :: a -> [b] <- phi2lists
  choice "enumListValueMaps" [
    ("maxMinCount", do
        phi :: Int -> Int <- oneOf "maxOrMin" [("max", \x -> -x), ("min", id)]
        pure $ \(x :: a) ->
          let vals :: [b] = phi2list x
              valsCounts :: [(Int, b)] = zip (List.counts vals) vals
          in if null vals then dflt else snd . head . sortOn (phi . fst) $ valsCounts)
    ]

-- TODO: this is *SYNTH* since it needs a spec
-- TODO: put elsewhere?
synthGroupIntLookupTables :: (Monad m, Eq a, Ord a, HasEnumIntFeatures m a, Eq b, Ord b, Show b) => Ex [a] -> ForTrain [b] -> SearchT m (ForTest [b])
synthGroupIntLookupTables inputs outputs = do
  phi2int <- enumIntFeatures
  pos2val :: Map Int b <- List.iterM (zip (Ex.train inputs) outputs) Map.empty $ \acc (inputs, outs) -> do
    -- TODO: choice point for negating? or ints responsibility?
    let ranks = List.indexInSorted (map phi2int inputs)
    List.iterM (zip ranks outs) acc $ \acc (rank, out) -> do
      case Map.lookup rank acc of
        Nothing   -> pure $ Map.insert rank out acc
        Just out2 -> guard (out == out2) *> pure acc
  guesses :: ForTest [b] <- liftO $ flip mapM (Ex.test inputs) $ \inputs -> do
    let ranks = List.indexInSorted (map phi2int inputs)
    flip mapM ranks $ \rank -> Map.lookup rank pos2val
  pure guesses
