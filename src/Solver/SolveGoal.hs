-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}

module Solver.SolveGoal where

import GHC.Generics (Generic, Generic1)
import System.IO.Unsafe (unsafePerformIO)
import Control.Exception.Base
import qualified Control.DeepSeq as DeepSeq
import Control.DeepSeq (($!!), NFData)
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import Util.Imports
import Search.SearchT
import Data.IORef
import Search.Guess
import qualified Data.Maybe as Maybe
import qualified Lib.Dims as Dims
import Search.ScoreFn
import Search.History (History(History))
import Search.DFS
import qualified System.Timeout
import qualified Search.Options
import Solver.SolveM
import qualified Solver.Options
import Solver.Synth1Context
import Solver.Goal
import qualified Data.Map as Map
import Synth.Ex (Ex, ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Dims (Dims(..))
import Lib.Color
import Solver.Tactics.All
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import qualified Solver.Goal as Goal
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Search.Guess as Guess
import Data.Time.Clock
import Data.Fixed

solve :: UTCTime -> IORef (Set (ForTest (Grid Color)), [Prediction (Grid Color)]) -> Int -> StdGoal -> SolveM (ForTest (Grid Color))
solve startTime guessRef fuel goal = do
  lift $ modify $ \s -> s { visitedGoals = Set.empty }
  solveGoal goal fuel >>= processGuess startTime guessRef

solveGoal goal@(Goal inputs outputs ctx) fuel
  | fuel <= 0 = do
      -- withHistory $ \history -> liftIO $ traceIO ("[solveGoal " ++ show fuel ++ "] " ++ show history ++ "\n" ++ show goal)
      guard $ all (uncurry (==)) $ zip (Ex.train inputs) outputs
      processTacticResult (TacticResult.Guess $ Ex.test inputs) 0

  | otherwise = do
      -- withHistory $ \history -> liftIO $ traceIO ("[solveGoal " ++ show fuel ++ "] " ++ show history ++ "\n" ++ show goal)
      sanityCheckGoal goal
      addString ("\n\n" ++ show goal ++ "\n\n") $ do
        if all (uncurry (==)) $ zip (Ex.train inputs) outputs
          then processTacticResult (TacticResult.Guess $ Ex.test inputs) 0
          else do
            (cost, tactic) <- oneOf "solveGoal" tactics
            guard $ cost <= fuel
            tacticResult <- tactic goal
            processTacticResult tacticResult (fuel - cost)

  where
    tactics = map (\(c, n, tac) -> (n, (c, tac))) [
      (1, "duplicate",                duplicate)
      , (1, "constOutput",            constOutput)
      , (1, "inputSymmetries",        inputSymmetries)
      , (1, "exactSubgrid",           exactSubgrid)
      , (1, "gravity",                gravity)
      , (1, "boolean",                boolean)
      , (1, "categorical",            categorical)
      , (1, "permutation",            permutation)
      , (1, "downscale",              downscale)
      , (1, "colorPartition",         colorPartition)
      , (1, "partition",              partition)
      , (1, "alignAxesLines",         alignAxesLines)
      , (1, "focus",                  focus)
      , (1, "removeOutputSymmetries", removeOutputSymmetries)
      , (1, "colorMap",               colorMap)
      , (1, "removeBackground",       removeBackground)
      , (1, "denoise",                denoise)
      , (1, "symmetrifyGrid",         symmetrifyGrid)
      , (1, "focusImputeRectangle",   focusImputeRectangle)
      , (1, "imputeBlanksByTiling",   imputeBlanksByTiling)
      , (1, "imputeBlanksLocal",      imputeBlanksLocal)
      , (1, "embed",                  embed)
      , (2, "upscale",                upscale)
      , (2, "fillInteriors",          fillInteriors)
      , (2, "shapeMap",               shapeMap)
      , (2, "motion",                 motion)
      , (1, "split",                  split)
      , (2, "colorBlast",             colorBlast)
      , (2, "axesBlast",              axesBlast)
      , (2, "rayBlast",               rayBlast)
      , (2, "neighborBlast",          neighborBlast)
      , (2, "modBlast",               modBlast)
      , (2, "shapeFeatureBlast",      shapeFeatureBlast)
      , (2, "classifyIndices",        classifyIndices)
      , (1, "dyeInputs",              dyeInputs)
      , (1, "alignAxesDims",          alignAxesLines)
      , (4, "monsterBlast",           monsterBlast)
      ]

    processTacticResult (TacticResult.Guess guess) _ = do
      sanityCheckGuesses goal guess
      pure guess

    processTacticResult (TacticResult.Decompose goal reconstruct) remainingFuel = do
      nestedGuesses <- solveGoal goal remainingFuel
      guesses <- liftIO . runMaybeT $ reconstruct nestedGuesses
      case guesses of
        Nothing -> do
          checksum <- lift $ asks ctxChecksum
          --withHistory $ \history -> liftIO . traceIO $ "[" ++ checksum ++ "] RECONSTRUCT FAILED:\n" ++ show history
          deadend ""
        Just guess -> pure guess

processGuess :: UTCTime -> IORef (Set (ForTest (Grid Color)), [Prediction (Grid Color)]) -> ForTest (Grid Color) -> SolveM (ForTest (Grid Color))
processGuess startTime guessRef guess = do
  guard $ flip all guess $ \guess -> Dims.all (Grid.dims guess) $ \idx ->
    let x = Grid.get guess idx in
      x >= 0 && x < 10
  (seen, guesses) <- liftIO $ readIORef guessRef
  guard . not . Set.member guess $ seen
  curTime :: UTCTime <- liftIO $ getCurrentTime
  let elapsed :: NominalDiffTime = diffUTCTime curTime startTime
  let nSeconds :: Float = fromRational . toRational $ elapsed
  withHistory $ \history -> liftIO $ modifyIORef guessRef $ \(seen, guesses) ->
    (Set.insert guess seen, (Prediction guess history nSeconds):guesses) -- gets reversed at end
  pure guess

data Prediction a = Prediction {
  guess    :: ForTest a,
  history  :: History,
  nSeconds :: Float
  } deriving (Eq, Show, Ord, Generic, NFData)

runSolver :: String -> Ex (Grid Color) -> ForTrain (Grid Color) -> Solver.Options.Options -> IO ([Prediction (Grid Color)], Bool)
runSolver checksum inputs outputs opts = do
  let synthCtx   = emptySynth1Context (length $ Ex.train inputs) (length $ Ex.test inputs)
  let goal       = Goal inputs outputs synthCtx
  startTime      <- getCurrentTime
  guessRef       <- newIORef (Set.empty, [])
  let psi        = iterativeDeepening (Solver.Options.schedule opts) $ \fuel -> solve startTime guessRef fuel goal
  let searchOpts = Search.Options.Options { Search.Options.maxGuesses = Solver.Options.maxGuesses opts }
  let sctx       = SolverContext checksum
  let sstate     = SolverState Set.empty Map.empty
  let mkGuess    = do
        guesses <- evalStateT (runReaderT (search psi searchOpts) sctx) sstate
        pure $!! DeepSeq.force guesses -- TODO: still doesn't seem to force!
  result <- System.Timeout.timeout (Solver.Options.timeoutSeconds opts * (10 ^ 6)) $! (handle handleNonTimeout mkGuess)
  guesses <- reverse . snd <$> readIORef guessRef
  pure (guesses, Maybe.isNothing result)

  where
    -- TODO: probably not needed anymore
    handleNonTimeout :: ArithException -> IO [Guess (ForTest (Grid Color))]
    handleNonTimeout e = do
      putStrLn $ "ARITH-ERROR[" ++ checksum ++ "]: " ++ show e
      pure []

    iterativeDeepening :: (Monad m, Show a) => [a] -> (a -> SearchT m b) -> SearchT m b
    iterativeDeepening schedule psi = choice "iterativeDeepening" $ map (\depth -> (show depth, psi depth)) schedule
