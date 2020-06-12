-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Downscale where

import Data.Vector.Unboxed.Base (Unbox)
import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Dims as Dims
import qualified Lib.BGrid as Box
import Lib.Dims (Dims (Dims))
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Lib.Color (Color)
import Data.List
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import Synth1.Arith
import Lib.Features
import Lib.Synth
import qualified Solver.Synth1Context as Synth1Context
import Solver.Synth1Context(ctxInts)
import qualified Synth.Spec as Spec
import Search.DFS
import Search.SearchT
import Synth.Basic
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.EagerFeatures
import Synth.LazyFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures

---------------
-- Downscale
---------------
-- Requires:
--   - FIXME
-- Considers:
--   - FIXME

downscale :: StdGoal -> SolveM TacticResult
downscale goal =
  choice "downscale" [
    ("input",  downscaleInputs goal),
    ("output", downscaleOutputs goal)
    ]

-- TODO: Return the grid of grids as well?
downscaleCore :: Grid Color -> Maybe Dims
downscaleCore g = do
  let m = Grid.nRows g
  let n = Grid.nCols g
  let idxsDesc :: [Dims] = map (uncurry Dims) $ [(km, kn) | km <- [m, (m - 1)..1], kn <- [n, (n - 1)..1]] -- cart prod
  flip List.first idxsDesc $ \dims@(Dims km kn) -> do
    guard $ m `rem` km == 0
    guard $ n `rem` kn == 0
    gc <- Grid.partitionEven (Dims (div m km) (div n kn)) (Dims km kn) g
    guard $ Int.all (Box.nRows gc * Box.nCols gc) $ \i ->
        let gcIdx = Dims.int2index (Box.dims gc) i in
          isJust (Grid.isUniform (Box.getG gc gcIdx))
    pure dims

downscaleInputs :: StdGoal -> SolveM TacticResult
downscaleInputs (Goal inputs outputs ctx) = find1 "downscaleInputs" $ do
  (inputScales :: Ex Dims) <- liftO $ flip Ex.mapM inputs $ downscaleCore
  guard $ flip List.majority (Ex.train inputScales) $ \(Dims x y) -> x > 1 || y > 1
  guard $ flip List.majority (Ex.test inputScales)  $ \(Dims x y) -> x > 1 || y > 1
  -- We synthesize only as a sanity check that it isn't too crazy of a function
  features <- lift . precompute . LazyFeatures.choose . getBasicLazyFeatures $ Ex.map Grid.dims inputs
  let spec :: ESpec (EagerFeatures Int) Dims = ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) (Ex.train inputScales)
  find1E "synthInts2Dims" $ synthInts2Dims spec
  newInputs :: Ex (Grid Color) <- flip Ex.mapM (Ex.zip inputs inputScales) $ \ (inGrid, innerDims) -> do
    partitionedInput :: Box.Grid (Grid Color) <- liftO $ Grid.partitionEvenInnerDims innerDims inGrid
    pure $ Grid.fromFunc (Box.dims partitionedInput) (\idx -> Grid.get (Box.get partitionedInput idx) (Index 0 0))
  pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure


downscaleOutputs :: StdGoal -> SolveM TacticResult
downscaleOutputs (Goal inputs outputs ctx) = find1 "downscaleOutputs" $ do
  outputScales :: ForTrain Dims <- liftO $ flip mapM outputs $ downscaleCore
  guard $ flip any outputScales $ \(Dims x y) -> x > 1 || y > 1
  features <- lift . precompute . LazyFeatures.choose . getBasicLazyFeatures $ inputs
  let spec :: ESpec (EagerFeatures Int) Dims = ESpec (Ex.getInfo inputs) (EagerFeatures $ ctxInts ctx ++ features) outputScales
  testDims <- find1E "synthInts2Dims" $ synthInts2Dims spec
  newOutputs :: ForTrain (Grid Color) <- flip mapM (zip outputScales outputs) $ \(innerDims, output) -> do
    partitionedOutput :: Box.Grid (Grid Color) <- liftO $ Grid.partitionEvenInnerDims innerDims output
    pure $ Grid.fromFunc (Box.dims partitionedOutput) (\idx -> Grid.getG (Box.get partitionedOutput idx) (Index 0 0))
  let reconstruct guesses = MaybeT . pure $ flip mapM (zip testDims guesses) $ \(innerDims, guess) -> do
        Grid.unpartitionEven (Grid.upscale guess innerDims)
  pure $ TacticResult.Decompose (Goal inputs newOutputs ctx) reconstruct
