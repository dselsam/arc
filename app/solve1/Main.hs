-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveDataTypeable, RecordWildCards, ScopedTypeVariables #-}
module Main where

import System.FilePath.Posix
import System.Directory
import System.Console.CmdArgs
import Frontend.ParseJSON
import Lib.Grid (Grid)
import Lib.Color (Color)
import Util.Imports
import qualified Lib.Grid as Grid
import qualified Synth.Ex as Ex
import Synth.Ex (Ex, ForTrain, ForTest)
import Search.SearchT
import Solver.SolveGoal (Prediction(Prediction))
import Search.Guess
import Solver.SolveGoal
import Frontend.Helpers
import qualified Solver.Options

data Args = Args {
  problem        :: FilePath,
  historiesDir   :: FilePath,
  timeoutSeconds :: Int,
  maxGuesses     :: Int,
  schedule       :: [Int]
  } deriving (Show, Data, Typeable)

defaultArgs = Args {
  problem        = "./thirdparty/ARC/data/training/6a1e5592.json",
  historiesDir   = "./histories/training",
  timeoutSeconds = 30,
  maxGuesses     = 1,
  schedule       = []
  }

main :: IO ()
main = do
  putStrLn "--- Solve1 ---"
  args <- cmdArgs defaultArgs
  print args
  when (null $ schedule args) $ error "NO SCHEDULE"
  (inputs, outputs) <- parseExample (problem args)
  let historiesPath = replaceDirectory (problem args) (historiesDir args)
  let opts = Solver.Options.Options {
        Solver.Options.timeoutSeconds = timeoutSeconds args,
        Solver.Options.maxGuesses     = maxGuesses args,
        Solver.Options.schedule       = schedule args
        }
  (guesses, timeout) <- runSolver (problem args) inputs (Ex.train outputs) opts
  when timeout $ putStrLn "\n-------- TIMEOUT --------\n"
  putStrLn $ "\n\n-----------------------"
  putStrLn $ "NUMBER OF GUESSES: " ++ show (length guesses)
  for_ guesses $ \(Prediction guess history _) -> do
    putStrLn $ "------------------------"
    putStrLn $ "HISTORY:\n\n" ++ show history
    putStrLn $ "GUESS: " ++ show guess
    if guess == Ex.test outputs then do
      putStrLn "CORRECT"
      writeFile (historiesPath) $ show history
    else do
      putStrLn "INCORRECT"
      for_ (zip guess (Ex.test outputs)) $ \(guess, output) ->
        print $ Grid.showGridDiff guess output
