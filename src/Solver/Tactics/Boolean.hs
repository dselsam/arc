-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Boolean where

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
import qualified Synth.Spec as Spec
import qualified Lib.Shape as Shape
import Search.DFS
import Synth.Basic
import Solver.Parse
import Synth.Core
import Synth.LazyFeatures
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.LazyFeatures as LazyFeatures
import Synth1.Basic
import Synth.Int2Bool
import Synth.Bool2Bool
import Synth.Sequence
import Solver.Synth1Context (ctxInts, ctxColors)

data BooleanOptions = BooleanOptions {
  minOutputs :: Int
  } deriving (Eq, Ord, Show)

defaultBooleanOptions :: BooleanOptions
defaultBooleanOptions = BooleanOptions { minOutputs = 4 }

boolean :: StdGoal -> SolveM TacticResult
boolean goal@(Goal inputs outputs ctx) = find1 "boolean" $ do
  guard $ length outputs >= minOutputs defaultBooleanOptions
  guard $ List.countDistinct id outputs == 2

  let output2inputs :: Map (Grid Color) [Grid Color] = List.iter (zip (Ex.train inputs) outputs) Map.empty $ \acc (input, output) -> pure $
        Map.insertWith (++) output [input] acc

  let (output2bool :: Map (Grid Color) Bool, bool2output :: Map Bool (Grid Color)) = List.iter (zip [0..] $ Map.keys output2inputs) (Map.empty, Map.empty) $ \(out2in, in2out) (i, output) -> pure $
        (Map.insert output (i==0) out2in, Map.insert (i==0) output in2out)

  let labels :: ForTrain Bool = flip map outputs $ \output -> output2bool Map.! output

  booleanGuesses <- choice "boolean" [
    ("ints", do
        x :: Ex Int <- choice "ints" [
          ("ctx",      oneOf "ctx" (ctxInts ctx)),
          ("inputs",   LazyFeatures.choose $ getBasicLazyFeatures inputs),
          ("intParse", LazyFeatures.choose $ getBasicIntParseFeatures inputs)
          ]
        synthInt2BoolE $ ESpec (Ex.getInfo inputs) x labels),
    ("bools", do
        b :: Ex Bool <- LazyFeatures.choose $ getBasicLazyFeatures inputs
        synthBool2BoolE $ ESpec (Ex.getInfo inputs) b labels)
    ]

  pure . TacticResult.Guess $ map (bool2output Map.!) (Ex.test booleanGuesses)
