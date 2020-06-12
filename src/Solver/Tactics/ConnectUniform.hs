-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ConnectUniform where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import Lib.Grid (Grid(..))
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Lib.Axis
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import qualified Lib.Axis as Axis
import qualified Lib.Direction as Direction
import Lib.Index (Index (Index))
import Synth1.Arith
import Synth1.Basic
import Lib.Features
import Lib.Synth
import qualified Solver.Synth1Context as Synth1Context
import Solver.Synth1Context(ctxInts)
import qualified Synth.Spec as Spec
import Search.DFS
import Search.SearchT
import Synth.Basic
import qualified Data.Set as Set
import Synth1.Basic
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)

---------------
-- Connect Uniform
---------------
-- Requires:
--   - FIXME
-- Considers:
--   - FIXME


uniformIdxPairsOnAx :: Grid Color -> Axis -> (Color -> Bool) -> [(Index, Index)]
uniformIdxPairsOnAx g@(Grid gDims gData) ax f = do
  let nonBlanks = Set.toList (Grid.nonBlankIdxs g)
  idx1 <- nonBlanks -- TODO: only enumerate along the actual axis, but may not be a problem in practice
  idx2 <- nonBlanks
  guard $ Axis.onSame ax idx1 idx2
  guard $ Axis.distAlongAxis ax idx1 idx2 > 1
  guard $ f (Grid.get g idx1) && f (Grid.get g idx2)
  guard $ (Grid.get g idx1) == (Grid.get g idx2)
  pure (idx1, idx2)


-- TODO:
-- as a bonus, we could even add a mask (we'd have to make sure it makes progress over the mask)
  -- simple map that checks subset relationship
-- "let idxsToColor" could use a mapM (and just get the trains) to guard earlier. If it passes, compute the tests.
-- should we be nub-bing somewhere?

-- slow!
connectUniform :: StdGoal -> SolveM TacticResult
connectUniform (Goal inputs outputs ctx) = find1 "connectUniform" $ do
  runSynth11 ctx $ do

    guard $ flip all (zip (Ex.train inputs) outputs) $ \(ig, og) -> Grid.sameDims ig og

    let masks :: Ex (Grid Bool) =
          if flip all (zip (Ex.train inputs) outputs) $ \(ig, og) -> Grid.subset ig og then
            flip Ex.map inputs $ \input -> Grid.map (\idx val -> (nonBlank val)) input
          else Ex.map (\input -> Grid.const (Grid.dims input) False) inputs

    -- we want to try all axes before we start restricting by color
    (indexPhis :: Ex (Color -> Bool)) <- choice "connectUniform.indexFn" [
      ("all", pure $ Ex.map (\_ -> (\_ -> True)) inputs)
      , ("isVal", do
            -- can restrict even more -- should only be those that appear in the INPUT
            -- shouldn't consider colors that only appear in the output
            cs <- Grid.enumRelevantColors inputs outputs
            pure $ flip Ex.map cs $ \c -> (\c1 -> c1 == c))
      ]

    -- we may want to not allow the "all" case -- it is just too unsafe
    (axes :: [Axis]) <- enumVals

    let uniformPairs :: Ex [(Axis, [(Index, Index)])] = flip Ex.map (Ex.zip inputs indexPhis) $ \(input, indexPhi) ->
          flip map axes $ \ax -> (ax, uniformIdxPairsOnAx input ax indexPhi)

    guard $ flip List.majority (Ex.toBigList uniformPairs) $ \axPairs ->
      flip any axPairs $ \(ax, pairs) -> not (null pairs)

    -- to decide what color to connect with (the "fill" color)
    -- note: only want to choose one after we know the axis set is fruitful
    (coloringFns :: Ex (Color -> Color)) <- choice "coloringFn" [
      ("id", pure $ Ex.map (\_ -> id) inputs)
      , ("const", do
          -- again, could restrict even more. Should only consider colors in the diff
          cs <- Grid.enumRelevantColors inputs outputs
          pure $ flip Ex.map cs (\c -> (\_ -> c)))
      ]


    -- lists of indices and what to color them
    -- for each input, a list of (set of indices, what to color that set of indices)
    let idxsToColor :: Ex [([Index], Color)] = flip Ex.map (Ex.zip3 uniformPairs inputs coloringFns) $ \(axPairs, ig, cf) ->
          concat $ flip map axPairs $ \(ax, pairs) ->
            flip map pairs $ \(idx1, idx2) -> (Direction.idxsBetween ax idx1 idx2, cf (Grid.get ig idx1))

    -- no allocated memory
    guard $ flip all (zip3 (Ex.train idxsToColor) outputs (Ex.train masks)) $ \(coloringInfo, og, mask) ->
      flip all coloringInfo $ \(idxs, c) -> flip all idxs $ \idx ->
        (Grid.get og idx) == c || (Grid.get mask idx)

    -- check that we're making a change on a majority of the inputs
    guard $ flip List.majority (zip3 (Ex.train inputs) (Ex.train idxsToColor) (Ex.train masks)) $ \(ig, coloringInfo, mask) ->
      flip any coloringInfo $ \(idxs, c) -> flip any idxs $ \idx ->
        (Grid.get ig idx) /= c && not (Grid.get mask idx)

    let coloredInputs :: Ex (Grid Color) = flip Ex.map (Ex.zip inputs idxsToColor) $ \(ig, coloringInfo) ->
          List.iter coloringInfo ig $ \acc (idxs, c) -> pure $ Grid.setIdxsToVal acc idxs c

    -- shouldn't fail -- Maybe.fromJust should be safe here if we wanted it
    (maskUnionNewInputs :: Ex (Grid Color)) <- liftO $ flip Ex.mapM (Ex.zip3 inputs coloredInputs masks) $ \(ig, cIg, mask) ->
          Grid.union (Grid.map (\idx b -> if b then Grid.get ig idx else blank) mask) cIg

    pure $ TacticResult.Decompose (Goal maskUnionNewInputs outputs ctx) pure
