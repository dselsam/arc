-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveDataTypeable, RecordWildCards, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module Frontend.Helpers where

import qualified Data.List as List
import Util.List (iter, range)
import qualified Util.List as List
import System.Directory
import System.IO
import System.Environment
import Control.Exception.Base
import System.FilePath.Posix
import Text.Printf
import Lib.Color (Color(Color))
import Lib.Grid (Grid(Grid))
import Synth.Ex (ForTrain, ForTest)
import Util.Imports
import Synth.Ex (ForTest)
import GHC.Generics (Generic)
import Control.DeepSeq
import Search.Guess
import Search.Entry (Entry(Entry))
import Solver.SolveGoal (Prediction(Prediction))
import qualified Search.History as History
import qualified Lib.Grid as Grid

data GuessStats = GuessStats {
  nHistories :: Int,
  nSeconds   :: Float
  } deriving (Eq, Ord, Show, Generic, NFData)

data GuessResult =
  GoodGuess GuessStats | BadGuess GuessStats | ErrorGuess String
  deriving (Eq, Ord, Show, Generic, NFData)

-- TODO: Bundle with a list of errors
data Result =
  Timeout
  | Error
  | CorrectAt [Int] GuessStats
  | BadGuesses Int GuessStats
  | NoGuesses
  deriving (Eq, Ord, Show, Generic, NFData)

allBadGuesses (BadGuesses _ _) = True
allBadGuesses _                = False

hasGoodGuess (CorrectAt _ _) = True
hasGoodGuess _               = False

guessToGuessResult :: FilePath -> FilePath -> Int -> String -> ForTest (Grid Color) -> (Int, Prediction (Grid Color)) -> IO GuessResult
guessToGuessResult guessesDir historiesDir i checksum outputs (guessNumber, Prediction guesses history nSec) = handle (handler i checksum) $ do
  let goodGuess :: Bool = all (uncurry (==)) (zip guesses outputs)
  h <- openFile (guessesDir </> ("g" ++ show guessNumber ++ (if goodGuess then "_good" else "_bad") ++ ".txt")) WriteMode
  hPutStrLn h $ "Checksum: " ++ take 8 checksum
  hPutStrLn h $ "Number of seconds: " ++ show nSec
  hPutStrLn h $ "Length of (outer) history: " ++ show (History.nOuters history)
  hPutStrLn h $ "Length of (full) history:  " ++ show (History.countRec (\_ -> True) history)
  hPutStrLn h $ "Number of solveGoals:      " ++ show (History.countRec (\(Entry cp c) -> cp == "solveGoal") history)
  hPutStrLn h $ "Number of decisionList:ite " ++ show (History.countRec (\(Entry cp c) -> cp == "decisionListE" && c == "ite") history)
  hPutStrLn h $ "Number of blast calls:     " ++ show (History.countRec (\(Entry cp c) -> cp == "solveGoal" && List.isSuffixOf "Blast" c) history)
  hPutStrLn h $ "\nHistory:\n\n" ++ show history
  hPutStrLn h $ "\n\nGuesses:\n\n" ++ show guesses
  hPutStrLn h $ "\n\nDiffs:\n\n"
  for_ (zip guesses outputs) $ \(guess, output) -> hPutStrLn h $ show $ Grid.showGridDiff guess output

  let stats = GuessStats { nHistories = History.nOuters history, nSeconds = nSec }
  if goodGuess then do
    writeFile (historiesDir </> checksum) $ show history
    pure $ GoodGuess stats
  else
    pure $ BadGuess stats
  where
    handler :: Int -> String -> SomeException -> IO GuessResult
    handler i checksum e = do
      putStrLn $ "\n -- [" ++ show i ++ "] ERROR: " ++ checksum ++ " " ++ show e ++ " --\n"
      pure $ ErrorGuess (show e)

guessesToResult :: FilePath -> FilePath -> Int -> String -> ForTest (Grid Color) -> [Prediction (Grid Color)] -> Bool -> IO Result
guessesToResult guessesDir historiesDir i checksum outputs  []     False = pure NoGuesses
guessesToResult guessesDir historiesDir i checksum outputs  []     True  = pure Timeout
guessesToResult guessesDir historiesDir i checksum outputs guesses _     = do
  createDirectory (guessesDir </> (take 8 checksum))
  guessResults <- mapM (guessToGuessResult (guessesDir </> (take 8 checksum)) historiesDir i checksum outputs) (zip [1..] guesses)
  let corrects = filter (\(_, r) -> case r of GoodGuess stats -> True; _ -> False) (zip [1..] guessResults)
  let bads     = filter (\(_, r) -> case r of BadGuess stats -> True; _ -> False) (zip [1..] guessResults)
  case corrects of
    [] -> pure $ BadGuesses (length bads) (case bads of (_, BadGuess stats):_ -> stats)
    (i, GoodGuess stats):guesses ->
      pure $ CorrectAt (i:map fst guesses) stats

printResults :: [String] -> [Result] -> IO ()
printResults checksums results = do
  let f rs = for_ rs $ \((i :: Int), checksum, result) ->
        putStrLn $ printf "%3d %8s %s" i (take 8 checksum) (show result)
  f . filter ((==Timeout)   . \(_, _, r) -> r) $ checks
  f . filter ((==Error)     . \(_, _, r) -> r) $ checks
  f . filter ((==NoGuesses) . \(_, _, r) -> r) $ checks
  f . filter (hasGoodGuess  . \(_, _, r) -> r) $ checks
  f . filter (allBadGuesses . \(_, _, r) -> r) $ checks
  putStrLn $ "----------------------------"
  putStrLn $ "#timeout:  " ++ (show . length . filter (==Timeout)   $ results)
  putStrLn $ "#error:    " ++ (show . length . filter (==Error)     $ results)
  putStrLn $ "#noguess:  " ++ (show . length . filter (==NoGuesses) $ results)
  putStrLn $ "#correct:  " ++ (show . length . filter hasGoodGuess  $ results)
  putStrLn $ "#badguess: " ++ (show . length . filter allBadGuesses $ results)

  where
    checks = zip3 [1..] checksums results

resultToCSV :: Result -> String
resultToCSV Timeout              = "timeout, -1"
resultToCSV Error                = "error, -1"
resultToCSV (CorrectAt _ stats)  = "correct, " ++ show (nSeconds stats)
resultToCSV (BadGuesses _ stats) = "badguess, " ++ show (nSeconds stats)
resultToCSV NoGuesses            = "noguess, -1"

guessesToSubmissionString :: String -> Int -> ForTest (Grid Color) -> String
guessesToSubmissionString checksum testNum guesses =

  checksum ++ "_" ++ (show testNum) ++ "," ++ guessesString
  where
    guessesString = iter (zip (range (length guesses)) guesses) "" $ \acc (i, guess) ->
      if i == (length guesses) - 1 then pure (acc ++ flattenGuess guess)
      else pure $ acc ++ flattenGuess guess ++ " "

flattenGuess :: Grid Color -> String
flattenGuess guess =
    iter (range (Grid.nRows guess)) "" $ \acc rowNum ->
      let rowString = iter (Grid.getRow guess rowNum) "" (\acc2 val -> pure (acc2 ++ (show val))) in
        if rowNum == (Grid.nRows guess) - 1 then pure (acc ++ rowString)
        else pure (acc ++ rowString ++ "|")

solveResultToSubmissionString :: String -> [ForTest (Grid Color)] -> String
solveResultToSubmissionString checksum [] = ""

solveResultToSubmissionString checksum allGuesses
  | not (List.allSame $ map length allGuesses) = ""
  | otherwise =
    let nOutputs = length (head allGuesses) in
      unlines $ flip map (range nOutputs) $ \i ->
        checksum ++ "_" ++ show i ++ ","
        ++ List.intercalate " " (flip map allGuesses (\guesses -> "|" ++ flattenGuess (guesses List.!! i) ++ "|"))
