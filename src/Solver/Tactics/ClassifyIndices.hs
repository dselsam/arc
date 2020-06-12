-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ClassifyIndices where

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
import Synth1.Basic
import Synth.Int2Bool
import Synth.Bool2Bool
import Synth.Sequence
import Solver.Tactics.GuessDims
import Solver.Synth1Context (ctxInts, ctxColors)

-- TODO: this is missing ones that the Lean version got.
-- I ported very very rushed, likely stupid mistakes.
-- TODO:
--   - when dims are the same, skip if-then-else and require the mask to make progress on the DIFFS

classifyIndices :: StdGoal -> SolveM TacticResult
classifyIndices goal@(Goal inputs outputs ctx) = choice "classifyIndices" [
  ("idx2idx", do
      testDims  <- synthDims goal
      idx2idx   <- enumIdx2Idx
      idx2color <- enumIdx2Color
      let f input idx = idx2color input (idx2idx idx)
      guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Dims.all (Grid.dims output) $ \idx -> Grid.get output idx == idx2color input (idx2idx idx)
      pure $ TacticResult.Guess . flip map (zip (Ex.test inputs) testDims) $ \(input, outDims) ->
        Grid.fromFunc outDims $ \idx -> idx2color input (idx2idx idx)),
  ("if2color", do
      -- uncomment below if we want to only do this choice if the dims are NOT the same
      --guard $ flip any (zip (Ex.train inputs) outputs) $ \(ig, og) -> not (Grid.sameDims ig og)
      testDims <- synthDims goal

      idx2bool <- enumIdx2Bool
      guard $ flip Ex.all (Ex.zip inputs $ Ex (map Grid.dims outputs) testDims) $ \(input, outDims) ->
        Dims.any outDims $ \idx -> idx2bool outDims idx
      guard $ flip Ex.all (Ex.zip inputs $ Ex (map Grid.dims outputs) testDims) $ \(input, outDims) ->
        Dims.any outDims $ \idx -> not $ idx2bool outDims idx

      true2color <- enumIdx2Color
      guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Dims.all (Grid.dims output) $ \idx -> idx2bool (Grid.dims output) idx <= (true2color input idx == Grid.get output idx)

      false2color <- enumIdx2Color
      guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Dims.all (Grid.dims output) $ \idx -> (not $ idx2bool (Grid.dims output) idx) <= (false2color input idx == Grid.get output idx)

      pure $ TacticResult.Guess . flip map (zip (Ex.test inputs) testDims) $ \(input, outDims) ->
        Grid.fromFunc outDims $ \idx ->
          if idx2bool outDims idx
          then true2color  input idx
          else false2color input idx)
  {-("if2colorSameDims", do
      -- should only do this choice if the dims ARE the same
      guard $ flip all (zip (Ex.train inputs) outputs) $ \(ig, og) -> Grid.sameDims ig og

      idx2bool <- enumIdx2Bool
      guard $ flip Ex.all inputs $ \ig -> Dims.any (Grid.dims ig) $ \idx -> idx2bool (Grid.dims ig) idx

      idx2color <- enumIdx2Color
      guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Dims.all (Grid.dims output) $ \idx -> idx2bool (Grid.dims output) idx <= (idx2color input idx == Grid.get output idx)

      let newInputs = flip Ex.map inputs $ \ig -> Grid.fromFunc (Grid.dims ig) $ \idx ->
            if idx2bool (Grid.dims ig) idx then idx2color ig idx else (Grid.get ig idx)

      -- guard that we are doing something new on a majority of the inputs
      -- we could be stricter with this if necessary
      -- this is especially necessary because currently classify indices doesn't make any greedy
      -- decisions -- it just picks the first one
      guard $ flip List.majority (zip (Ex.toBigList inputs) (Ex.toBigList newInputs)) $ \(ig, newIg) ->
        ig /= newIg

      if flip all (zip (Ex.train newInputs) outputs) (\(ig, og) -> ig == og) then
        pure $ TacticResult.Guess (Ex.test newInputs)
      else
        pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure)-}
  ]

enumIdx2Int :: SolveM (Index -> Int)
enumIdx2Int = oneOf "enumIdx2Int" [
  ("row",  Index.row),
  ("col",  Index.col),
  ("sum",  \(Index r c) -> r + c),
  ("diff", \(Index r c) -> r - c),
  ("max",  \(Index r c) -> max r c),
  ("min",  \(Index r c) -> min r c)
  ]

enumInt2Bool :: SolveM (Int -> Bool)
enumInt2Bool = do
  phi <- oneOf "enumInt2Bool.core" [
    ("isZero",   (==0)),
    ("isNegOne", (==(-1))),
    ("isOne",    (==1)),
    ("isTwo",    (==2)),
    ("isEven",   ((==0) . (`mod` 2))),
    ("isOdd" ,   ((==1) . (`mod` 2))),
    ("is0m3" ,   ((==0) . (`mod` 3))),
    ("is1m3" ,   ((==1) . (`mod` 3))),
    ("is2m3" ,   ((==2) . (`mod` 3))),
    ("isGt0" ,   (>0)),
    ("isGt1" ,   (>1))
    ]
  neg <- oneOf "enumInt2Bool.neg" [("no", id), ("yes", not)]
  pure $ neg . phi

enumIdx2Color :: SolveM (Grid Color -> Index -> Color)
enumIdx2Color = choice "enumIdx2Color" [
  ("blank", pure $ \_ _ -> blank),
  ("keep",  pure $ \input (Index x y) -> let Dims dx dy = Grid.dims input in Grid.get input (Index (x `mod` dx) (y `mod` dy))),
  ("constUpdate", do
      c <- enumVals
      pure $ \input (Index x y) ->
        let Dims dx dy = Grid.dims input in
          if nonBlank (Grid.get input (Index (x `mod` dx) (y `mod` dy)))
          then c
          else blank),
  ("const", do
      c <- enumVals
      pure $ \input (Index x y) -> c)
  ]

enumIdx2Bool :: SolveM (Dims -> Index -> Bool)
enumIdx2Bool = choice "enumIdx2Bool" [
  ("idx2int2bool", do
      idx2int  <- enumIdx2Int
      int2bool <- enumInt2Bool
      pure $ \_ idx -> int2bool $ idx2int idx),
  ("idx2bool", oneOf "idx2bool" [
      ("middleRow",  \(Dims m n) (Index i j) -> i == m `div` 2)
      , ("middleCol",  \(Dims m n) (Index i j) -> j == n `div` 2)
      , ("upperLeft",  \(Dims m n) (Index i j) -> i == 0 && j == 0)
      , ("lowerRight", \(Dims m n) (Index i j) -> i == m-1 && j == n-1)
      , ("onEdge", \ds idx -> Dims.onEdge ds idx)
      ])
  ]

enumIdx2Idx :: SolveM (Index -> Index)
enumIdx2Idx = oneOf "enumIdx2Idx" [
  ("id",        id),
  ("transpose", Index.transpose),
  ("max",       \(Index i j) -> Index (max i j) (max i j)),
  ("min",       \(Index i j) -> Index (min i j) (min i j))
  ]
