-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Categorical where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import qualified Data.Maybe as Maybe
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Lib.Dims (Dims (Dims))
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import qualified Data.Map as Map
import Lib.Index (Index (Index))
import Synth1.Arith
import Search.SearchT
import Lib.Blank
import qualified Lib.Parse as Parse
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Solver.Parse
import Solver.Tactics.GuessDims
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec as Spec
import Search.DFS
import Synth.Basic
import Synth.Core
import Synth1.Basic
import Synth.Sequence
import Solver.Synth1Context (ctxInts, ctxColors)
import Synth.EagerFeatures
import Synth.LazyFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures

data CategoricalOptions = CategoricalOptions {
  minRepeatedOutputs :: Int,
  minDistinctOutputs :: Int
  } deriving (Eq, Ord, Show)

defaultCategoricalOptions :: CategoricalOptions
defaultCategoricalOptions = CategoricalOptions { minRepeatedOutputs = 2, minDistinctOutputs = 3 }

categorical :: StdGoal -> SolveM TacticResult
categorical goal@(Goal inputs outputs ctx) = find1 "categorical" $ do
  let output2inputs :: Map (Grid Color) [Grid Color] = List.iter (zip (Ex.train inputs) outputs) Map.empty $ \acc (input, output) -> pure $
        Map.insertWith (++) output [input] acc
  guard $ (length . filter ((>1) . length) $ Map.elems output2inputs) >= (minRepeatedOutputs defaultCategoricalOptions)
  guard $ Map.size output2inputs >= (minDistinctOutputs defaultCategoricalOptions)

  let (output2idx :: Map (Grid Color) Int, idx2output :: Map Int (Grid Color)) = List.iter (zip [0..] $ Map.keys output2inputs) (Map.empty, Map.empty) $ \(out2in, in2out) (i, output) -> pure $
        (Map.insert output i out2in, Map.insert i output in2out)

  let labels :: ForTrain Int = flip map outputs $ \output -> output2idx Map.! output

  categoricalGuesses <- choice "categorical" [
    ("ints", do
        -- TODO: we don't actually want to precompute here, since we aren't using a synth call that makes use of the group
        x :: Ex Int <- LazyFeatures.choose . getBasicLazyFeatures $ inputs
        lookupTableE $ ESpec (Ex.getInfo inputs) x labels),
    ("colors", do
        x :: Ex Color <- LazyFeatures.choose . getBasicLazyFeatures $ inputs
        lookupTableE $ ESpec (Ex.getInfo inputs) x labels),
    ("self", lookupTableE $ ESpec (Ex.getInfo inputs) inputs labels),
    ("bitGrids", lookupTableE $ flip (ESpec (Ex.getInfo inputs)) labels $
                   Ex.map (\input -> flip Grid.map input $ \idx x -> nonBlank x) inputs)
    ]

  pure . TacticResult.Guess $ map (idx2output Map.!) (Ex.test categoricalGuesses)
