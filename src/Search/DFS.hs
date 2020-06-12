-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Search.DFS where

import Util.Imports
import Control.Monad.IO.Class
import qualified Util.List as List
import qualified Data.List as List
import Control.Monad.Except (ExceptT, lift, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State (StateT, get, modify, runStateT, evalStateT)
import Search.Entry (Entry(Entry))
import qualified Search.Entry as Entry
import Search.History (History)
import qualified Search.History as History
import Search.Guess (Guess(Guess))
import qualified Search.Guess as Guess
import Search.ScoreFn
import Search.SearchT
import qualified Search.Options
import Util.LList (LList(LList))
import qualified Util.LList as LList

data Continuation m a = Continuation { psi :: SearchT m a, history :: History }

data State m a = State {
  stack     :: [Continuation m a],
  guesses   :: LList (Guess a),
  nVisited  :: Int,
  nFailed   :: Int
  }

type DFS m b a = ReaderT Search.Options.Options (StateT (State m b) m) a

finish :: (Monad m) => DFS m a [Guess a]
finish = LList.toList . guesses <$> get

searchM :: (Monad m) => DFS m a [Guess a]
searchM = do
  s <- get
  case stack s of
    [] -> finish
    (Continuation (SearchT f) history):rest -> do
      -- traceM ("[searchM] " ++ show (length (stack s)) ++ " history: " ++ show history)
      modify $ \s -> s { nVisited = nVisited s + 1, stack = rest }
      result <- lift . lift $ f
      case result of
        Fail -> do
          modify $ \s -> s { nFailed = nFailed s + 1 }
          searchM
        Pop i psi -> do
          modify $ \s -> s { stack = (Continuation psi history):drop i (stack s) }
          searchM
        WithHistory psi -> do
          modify $ \s -> s { stack = (Continuation (psi history) history):(stack s) }
          searchM
        AddHistory name h psi -> do
          modify $ \s -> s {stack = (Continuation psi $ History.addHistory name h history):(stack s) }
          searchM
        AddString str psi -> do
          modify $ \s -> s {stack = (Continuation psi $ History.addString str history):(stack s) }
          searchM
        Done val -> do
          s <- get
          let guess = Guess {
                Guess.value      = val,
                Guess.history    = history,
                Guess.nVisited   = nVisited s,
                Guess.nFailed    = nFailed s
                }
          modify $ \s -> s { guesses = LList.cons guess (guesses s) }
          maxGuesses <- asks Search.Options.maxGuesses
          s <- get
          if LList.size (guesses s) >= maxGuesses then finish else searchM
        ChoicePoint cp cs -> do
          for_ (reverse cs) $ \(c, psi) -> modify $ \s -> s { stack = (Continuation psi (History.addEntry (Entry cp c) history)):(stack s) }
          searchM

search :: (Monad m) => SearchT m a -> Search.Options.Options -> m [Guess a]
search psi opts = do
  let s = State [Continuation psi History.empty] LList.empty 0 0
  reverse <$> evalStateT (runReaderT searchM opts) s

find1 :: (Monad m) => String -> SearchT m a -> SearchT m a
find1 name psi = do
  let opts = Search.Options.Options 1
  [Guess { Guess.value = value, Guess.history = history }] <- lift $ search psi opts
  addHistory name history $ pure value

find1O :: (Monad m) => String -> SearchT m a -> SearchT m (Maybe a)
find1O name psi = do
  let opts = Search.Options.Options 1
  result <- lift $ search psi opts
  case result of
    [] -> pure Nothing
    [Guess { Guess.value = value, Guess.history = history }] ->
      addHistory name history $ pure (Just value)

enumAll :: (Monad m) => SearchT m a -> m [a]
enumAll psi = map Guess.value <$> enumAllG psi

enumAllG :: (Monad m) => SearchT m a -> m [Guess a]
enumAllG psi = do
  let opts = Search.Options.Options { Search.Options.maxGuesses = 1000000000000 }
  search psi opts

findBestsOnK :: (Monad m, Ord b) => String -> [Choice (a -> b)] -> SearchT m a -> SearchT m a
findBestsOnK name keys psi = findBestsOn name (map (onSndWith comparing) keys) psi

findBestsOn :: (Monad m) => String -> [Choice (a -> a -> Ordering)] -> SearchT m a -> SearchT m a
findBestsOn name cmps psi = do
  let opts = Search.Options.Options { Search.Options.maxGuesses = 100000000000 }
  guesses <- lift $ search psi opts
  guard . not . null $ guesses
  let allBests    = flip map cmps $ \(n, cmp) -> (n, head $ flip List.sortBy (zip [1..] guesses) $ \(_, guess1) (_, guess2) -> cmp (Guess.value guess1) (Guess.value guess2))
  let uniqueBests = List.stableUniqKey (\(n, (i, guess)) -> i) allBests
  choice "findBestsOn" $ map (\(n, (i, guess)) -> (n, addHistory n (Guess.history guess) (pure $ Guess.value guess))) uniqueBests

findBestOn :: (Monad m) => String -> (a -> Int) -> SearchT m a -> SearchT m a
findBestOn name key = findBest name (comparing key)

findBest :: (Monad m) => String -> (a -> a -> Ordering) -> SearchT m a -> SearchT m a
findBest name cmp psi = do
  let opts = Search.Options.Options { Search.Options.maxGuesses = 100000000000 }
  guesses <- lift $ search psi opts
  guard . not . null $ guesses
  let Guess { Guess.value = value, Guess.history = history } = head . List.sortBy (\guess1 guess2 -> cmp (Guess.value guess1) (Guess.value guess2)) $ guesses
  addHistory name history $ pure value

precompute :: (Monad m, Ord a) => SearchT m a -> m [Choice a]
precompute psi = do
  let opts = Search.Options.Options 100000000000
  results <- search psi opts
  let uniqueResults = List.stableUniqKey Guess.value results
  pure $ map (\guess -> (History.showCondensed $ Guess.history guess, Guess.value guess)) uniqueResults
