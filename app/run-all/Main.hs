-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveDataTypeable, RecordWildCards, ScopedTypeVariables #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Exception.Base
import System.FilePath.Posix
import System.Directory
import System.Random
import System.Console.CmdArgs
import Frontend.ParseJSON
import Lib.Grid (Grid)
import Lib.Color (Color)
import Text.Printf
import Control.Monad (filterM)
import Util.Imports
import qualified Lib.Grid as Grid
import qualified Synth.Ex as Ex
import Synth.Ex (Ex, ForTrain, ForTest)
import Solver.SolveGoal
import qualified System.Timeout
import Control.Concurrent.PooledIO.Final as PooledIO
import Frontend.Helpers
import qualified Solver.Options
import Data.Time.Clock
import Debug.Trace
import GitHash (giHash, getGitInfo)

data Args = Args {
  problemDir      :: FilePath,
  historiesDir    :: FilePath,
  oldHistoriesDir :: Maybe FilePath,
  resultsCSV      :: FilePath,
  nameOfRun       :: String,
  gitRootDir      :: FilePath,
  guessesDirPfix  :: FilePath,
  timeoutSeconds  :: Int,
  maxGuesses      :: Int,
  schedule        :: [Int],
  v               :: FilePath
  } deriving (Show, Data, Typeable)

defaultArgs = Args {
  problemDir      = "./thirdparty/ARC/data/",
  historiesDir    = "./histories/",
  resultsCSV      = "./results.csv",
  nameOfRun       = "default-name",
  gitRootDir      = ".",
  oldHistoriesDir = Nothing,
  guessesDirPfix  = "./guesses/",
  timeoutSeconds  = 1000,
  maxGuesses      = 3,
  schedule        = [],
  v               = "training"
  }

main :: IO ()
main = do
  args <- do
    tmpArgs <- cmdArgs defaultArgs

    let tmpArgs2 = tmpArgs { historiesDir = (historiesDir tmpArgs) </> (v tmpArgs),
                              problemDir = (problemDir tmpArgs) </> (v tmpArgs) }

    let tmpArgs3 = case oldHistoriesDir tmpArgs of
                     Nothing -> tmpArgs2 {oldHistoriesDir = Just $ historiesDir tmpArgs2}
                     (Just oldHistories) -> tmpArgs2 {oldHistoriesDir = Just $ oldHistories </> (v tmpArgs)}

    pure tmpArgs3

  print args
  when (null $ schedule args) $ error "NO SCHEDULE"

  let oldHistories = case oldHistoriesDir args of Just x -> x; Nothing -> fail ""
  createDirectoryIfMissing True (historiesDir args)
  doesDirectoryExist oldHistories >>= guard
  createDirectoryIfMissing True (guessesDirPfix args)
  checksums <- filter (\path -> length path == 13) <$> listDirectory (problemDir args)
  let opts = Solver.Options.Options {
        Solver.Options.timeoutSeconds = timeoutSeconds args,
        Solver.Options.maxGuesses     = maxGuesses args,
        Solver.Options.schedule       = schedule args
        }

  guessRunName <- randomStr 8
  Right gitInfo <- getGitInfo (gitRootDir args)
  let commit = take 6 (giHash gitInfo)
  let guessesDir :: FilePath = (guessesDirPfix args) </> ("run_" ++ commit ++ "_" ++ nameOfRun args)
  createDirectory guessesDir

  results <- PooledIO.run $ do
    -- TODO: not sure if this will catch or not
    flip traverse (zip [1..] checksums) $ \(i, checksum) -> PooledIO.fork $ handle (handleAny checksum) $ do
      putStrLn $ printf "[%3d] START %8s" i (take 8 checksum)
      (inputs, outputs) <- parseExample (problemDir args </> checksum)
      -- Note: we are trusting the Solver to respect the timeout
      (guesses, timeout) <- runSolver checksum inputs (Ex.train outputs) opts
      result <- guessesToResult guessesDir (historiesDir args) i checksum (Ex.test outputs) guesses timeout
      putStrLn $ printf "[%3d] END   %8s %s" i (take 8 checksum) (show result)
      pure result

  putStrLn $ "\nFailed regressions:\n"
  notGettingButWasGetting :: [(Int, String, Result)] <- flip filterM (zip3 [1..] checksums results) $ \(i, checksum, result) ->
    if hasGoodGuess result then pure False else doesFileExist (oldHistories </> checksum)
  for_ notGettingButWasGetting $ \(i, checksum, result) ->
        putStrLn $ printf "[%3d] %8s %s" i (take 8 checksum) (show result)

  let timedOutButWasGetting = flip filter notGettingButWasGetting $ \(i, checksum, result) -> result == Timeout

  printResults checksums results
  putStrLn $ "#failed regressions: " ++ (show $ length notGettingButWasGetting)
  putStrLn $ "#failed non-timeout regressions " ++ (show $ (length notGettingButWasGetting) - (length timedOutButWasGetting))

  appendCSV args checksums results

  where
    handleAny :: String -> SomeException -> IO Result
    handleAny checksum e = do
      print $ "OUTER-ERROR[" ++ show checksum ++ ": " ++ show e
      pure Error

    appendCSV args checksums results = do
      time <- getCurrentTime
      Right gitInfo <- getGitInfo (gitRootDir args)
      let commit = take 6 (giHash gitInfo)
      let runName = if nameOfRun args == "default-name" then commit else nameOfRun args
      let csv = unlines $ map (\(checksum, result) -> show (runName) ++ ", " ++ show commit ++ ", \"" ++ show time ++ "\", " ++ (take 8 checksum) ++ ", " ++ resultToCSV result) (zip checksums results)
      appendFile (resultsCSV args) csv

randomStr :: Int -> IO String
randomStr k = take k <$> randomRs ('a','z') <$> newStdGen
