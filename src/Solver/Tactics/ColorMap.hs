-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ColorMap where

import Data.Vector.Unboxed.Base (Unbox)
import Util.Imports
import qualified Util.List as List
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(Ex), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Line as Line
import Lib.Blank
import Lib.Axis
import Lib.Grid (Grid(dims))
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import Solver.TacticResult (TacticResult(..))
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import qualified Data.HashTable.ST.Basic as H
import Control.Monad.ST
import Data.STRef
import qualified Data.Map as Map
import qualified Util.Map as Map
import Control.Monad.Fail (MonadFail)
import qualified Data.Set as Set
import qualified Data.List as List

colorMap :: StdGoal -> SolveM TacticResult
colorMap goal@(Goal inputs outputs ctx) = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)

  colorMaps :: ForTrain (Map Color Color) <- do
    choice "buildTrainMaps" [
      ("buildPointwiseMaps", buildPointwiseMaps)]

  guard . not . all (all (uncurry (==))) $ map Map.assocs colorMaps

  testMaps <- runSynth11 ctx $ synthG2C2C inputs colorMaps

  guessOutputs <- liftO $ flip mapM (zip testMaps $ Ex.test inputs) $ \(testMap, input) ->
    Grid.mapM (\_ c -> Map.lookup c testMap) input

  pure $ Guess guessOutputs

  where
    buildPointwiseMaps :: SolveM (ForTrain (Map Color Color))
    buildPointwiseMaps = flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) ->
      Dims.iterM (Grid.dims input) Map.empty $ \acc idx ->
        case Map.lookup (Grid.get input idx) acc of
          Nothing -> pure $ Map.insert (Grid.get input idx) (Grid.get output idx) acc
          Just c2 -> guard (c2 == Grid.get output idx) *> pure acc

synthG2C2C :: (Unbox a, HasBlank a) => (Ord a) => (Show a) => Ex (Grid a) -> ForTrain (Map a a) -> Synth1M (ForTest (Map a a))
synthG2C2C inputs trainMaps = choice "synthG2C2C" [
  ("constantColorMap", constantColorMap),
  ("swap",             swapColorMap),
  ("twoColorMap",      twoColorMap)]

    where
      constantColorMap = replicate (length $ Ex.test inputs) <$> liftO (do
        globalMap <- Map.glueMaps trainMaps
        guard $ flip any (Map.assocs globalMap) $ \(c1, c2) -> not $ c1 == c2
        pure globalMap)

      swapColorMap = do
        guard $ flip all trainMaps $ \map ->
          (Map.size map == 2 && let [(k1, v1), (k2, v2)] = Map.assocs map in k1 == v2 && v1 == k2)
        flip mapM (Ex.test inputs) $ \input -> do
          let colors = Grid.distinctVals (\_ -> True) input
          guard (Set.size colors == 2)
          let [x, y] = Set.toList colors
          pure $ Map.fromList [(x, y), (y, x)]

      {- `twoColorMap` will fire if all inputs have two nonblank colors.
          it will attempt to synthesize a function pixel-by-pixel,
          first checking if the value can be inferred from the intersection of the train maps,
          then trying to assign the "other color". It solves `f76d97a5` and easier swap problems
          such as `b94a9452`. -}

      twoColorMap = do
        inputColors :: Ex (Set a) <- flip Ex.mapM inputs $ \input -> do
          let cs = Grid.distinctVals nonBlank input
          guard $ Set.size cs == 2
          pure cs

        let otherColor :: Ex a -> Ex a = \colors ->
              flip Ex.map (Ex.zip colors inputColors) $ \(c, cs) -> Set.elemAt 0 $ (Set.delete c cs)

        (c1 :: Ex a) <- choice "pickFirstColor" [
          ("pickCommonColor", do
              c1 <- liftO $ flip List.find (Set.toList . head . Ex.test $ inputColors) $ \c ->
                flip all (Ex.toBigList inputColors) $ \cs -> c `Set.member` cs
              pure $ Ex.replicate (Ex.getInfo inputColors) c1),
          ("pickArbitraryColor", pure $ flip Ex.map inputColors $ \cs -> Set.elemAt 0 cs)]

        -- these synth calls are responsible for checking the guesses
        let synthGuesses :: Ex a -> Synth1M (ForTest a)
            synthGuesses cs =
              let checkGuesses cs vs = flip all (zip (Ex.train cs) (zip (Ex.train vs) trainMaps)) $ \(c,(v,d)) -> (Map.!) d c == v in
              choice "synthGuesses" [
              ("fromTrainMaps", fromTrainMaps cs),
              ("fromOther", do
                  let otherCs = otherColor cs
                  guard $ flip all (zip trainMaps (zip (Ex.train cs) (Ex.train otherCs))) $ \(trainMap, (c, otherC)) ->
                    case Map.lookup c trainMap of Nothing -> False; (Just v) -> v == otherC
                  pure $ Ex.test otherCs)]

            fromTrainMaps cs = choice "fromTrainMaps" [
              ("fromTestValues", flip mapM (Ex.test cs) $ \c -> do
                vs <- flip mapM trainMaps $ \trainMap -> liftO $ Map.lookup c trainMap
                guard $ Set.size (Set.fromList vs) == 1
                pure $ head vs),
              ("fromTrainValues", do
                  vs <- flip mapM (zip (Ex.train cs) trainMaps) $ \(c, trainMap) -> liftO $ Map.lookup c trainMap
                  guard $ Set.size (Set.fromList vs) == 1
                  pure $ replicate (length $ Ex.test cs) (head vs))]

        c1Guesses <- synthGuesses c1
        let c2 = otherColor c1
        c2Guesses <- synthGuesses c2

        -- now try to synthesize an output for blank inputs,
        -- then shove everything into a Map and return it

        -- @jesse What is going on here? Why are you using function graphs instead of Data.Map?
        -- Why is there this special case for blanks here? Seems like there could be support for
        -- (blank -> uniform) and (blank -> nonUniform) throughout.
        (guessesAux :: ForTest [(a,a)]) <- do
          let functionGraphs = (\(a,b) -> [a,b]) <$> zip (zip (Ex.test c1) c1Guesses) (zip (Ex.test c2) c2Guesses)
          if flip Ex.all inputs $ \input -> Grid.containsVal blank input
            then do
              blankGuesses <- fromTrainMaps $ flip Ex.map c1 $ \c -> blank
              pure $ (\(a,b) -> a ++ [b]) <$> zip functionGraphs (zip (replicate (length blankGuesses) blank) blankGuesses)
            else pure $ functionGraphs

        pure $ flip map guessesAux $ \pairs -> List.iter pairs Map.empty $ \acc (c,v) -> pure $ (Map.insert c v) acc
