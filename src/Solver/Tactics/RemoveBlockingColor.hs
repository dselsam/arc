-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.RemoveBlockingColor where

import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Data.Map as Map
import qualified Util.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Solver.Synth1Context (Synth1Context(..))
import Synth1.Basic
import Lib.Blank (isBlank, blank, nonBlank)
import Solver.Tactics.Identity (identity)
import qualified Search.SearchT as SearchT
import Search.SearchT (Result(..))

import Debug.Trace


data RemoveBlockingColorOpts = RemoveBlockingColorOpts { keepThreshold :: Float }

defaultRemoveBlockingColorOpts = RemoveBlockingColorOpts 0.5

getBlockingColors :: StdGoal -> SolveM (ForTrain (Set Color), ForTrain (Set Color))
getBlockingColors goal@(Goal inputs outputs ctx) = unzip <$> (do
  flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) -> do
    guard $ Grid.sameDims input output
    (keeps, (nonKeeps, keepCount), conflictMap) <- Dims.iterM (Grid.dims input) (Set.empty,(Set.empty,0), Map.empty) $ \(accKeeps, (accNonKeeps, accKeepCount), accConflictMap) idx -> do
      let cIn = Grid.get input idx
      let cOut = Grid.get output idx
      if cIn == cOut
        then let newAccKeeps = -- if isBlank cIn then accKeeps else 
                   Set.insert cIn accKeeps in
               pure $ (newAccKeeps, (accNonKeeps, accKeepCount+1), accConflictMap)
        else -- guard (cIn /= blank) *>
          let newAccConflictMap = case Map.lookup cIn accConflictMap of
                Nothing -> Map.insert cIn (Set.singleton cOut) accConflictMap
                (Just conflicts) -> Map.insert cIn (Set.insert cOut conflicts) accConflictMap
          in
            pure (accKeeps, (Set.insert cIn accNonKeeps, accKeepCount), newAccConflictMap) 
    let guardThreshold opts = guard $ (keepThreshold opts) < (fromIntegral keepCount)/(fromIntegral $ Grid.nCells input)
    guard $ not . Set.null $ keeps
    guardThreshold defaultRemoveBlockingColorOpts
    guard $ Map.iter conflictMap True $ \acc cIn cOuts -> (acc &&) . isJust $ do
      guard $ (Set.size cOuts == 1) <= (nonBlank $ Set.elemAt 0 cOuts)
    pure (nonKeeps, keeps))

removeBlockingColor :: StdGoal -> SolveM TacticResult
removeBlockingColor goal@(Goal inputs outputs ctx) = do
  removeColors :: Ex Color <- do
    trainColors <- flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) -> do
      (keeps, (nonKeeps, keepCount)) <- Dims.iterM (Grid.dims input) (Set.empty,(Set.empty,0)) $ \(accKeeps, (accNonKeeps, accKeepCount)) idx -> do
        let cIn = Grid.get input idx
        let cOut = Grid.get output idx
        if cIn == cOut
          then let newAccKeeps = if isBlank cIn then accKeeps else Set.insert cIn accKeeps in
                 pure $ (newAccKeeps, (accNonKeeps, accKeepCount+1))
          else guard (cIn /= blank) *> pure (accKeeps, (Set.insert cIn accNonKeeps, accKeepCount))
      let guardThreshold opts = guard $ (keepThreshold opts) < (fromIntegral keepCount)/(fromIntegral $ Grid.nCells input)
      guard $ Set.size nonKeeps == 1
      guard $ not . Set.null $ keeps
      guardThreshold defaultRemoveBlockingColorOpts
      let c = Set.elemAt 0 nonKeeps
      guard $ not $ c `Set.member` keeps
      guard $ not $ c `Set.member` Grid.distinctVals nonBlank output
      pure c

    guard $ Set.size (Set.fromList trainColors) == 1
    let removeColor = head trainColors
    guard $ flip all (Ex.test inputs) $ \input -> Grid.containsVal removeColor input

    -- liftIO . traceIO $ "REMOVING BLOCKING COLOR: " ++ show removeColor
    pure $ Ex trainColors $ replicate (length $ Ex.test inputs) $ removeColor

  let newInputs = flip Ex.map (Ex.zip inputs removeColors) $ \(input, c0) -> flip Grid.map input $ \idx c ->
        if c == c0 then blank else c
  let newCtx = ctx {ctxColors = ("removeBlockingColor", removeColors):(ctxColors ctx)}

  -- liftIO . traceIO $ "REMOVE BLOCKING COLOR SUCCEEDED"
  pure $ TacticResult.Decompose (Goal newInputs outputs newCtx) pure
