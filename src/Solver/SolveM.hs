-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData #-}
module Solver.SolveM (CoreM, SolveM, Synth1CoreM, Synth1M, oneOf, choice, liftO, SolverContext(..), SolverState(..),
                      runSynth1, runSynth11, runSynth1All) where

import Util.Imports
import qualified Util.List as List
import Search.ScoreFn
import qualified Search.Options
import Search.Guess
import Search.SearchT
import Search.DFS
import Synth1.Basic
import Lib.Color
import Lib.Blank
import Solver.Goal
import Lib.Grid (Grid)
import Synth1.Synth1Context
import Solver.Synth1Context
import Lib.Shape (Shape)
import Solver.Goal
import qualified Lib.Parse as Parse

-- Note: these are *global* across the multiverse
data SolverContext = SolverContext {
  ctxChecksum :: String
  } -- TODO: blastConfig

data SolverState = SolverState {
  visitedGoals   :: Set StdGoal, -- TODO: HashSet?
  parseCache     :: Map (Grid Color, Parse.Options) [Shape Color]
  }

type CoreM  = ReaderT SolverContext (StateT SolverState IO)
type SolveM = SearchT CoreM

type Synth1CoreM = ReaderT Synth1Context IO
type Synth1M = SearchT Synth1CoreM

instance HasSynth1Context (ReaderT Synth1Context IO) Color where
  synthCtx = do
    cs <- lift $ asks ctxColors
    oneOf "ctxColors" cs

instance HasSynth1Context (ReaderT Synth1Context IO) Int where
  synthCtx = do
    cs <- lift $ asks ctxInts
    oneOf "ctxInts" cs

instance HasTrainTest (ReaderT Synth1Context IO) where
  getNumTrain = lift $ asks ctxNumTrain
  getNumTest  = lift $ asks ctxNumTest

runSynth1 :: Synth1Context -> Synth1M a -> Int -> IO [Guess a]
runSynth1 ctx psi maxGuesses =
  let opts = Search.Options.Options { Search.Options.maxGuesses = maxGuesses } in
    flip runReaderT ctx $ search psi opts

runSynth1All :: Synth1Context -> Synth1M a -> IO [Guess a]
runSynth1All ctx psi = runSynth1 ctx psi 100000000000

runSynth11 :: Synth1Context -> Synth1M a -> SolveM a
runSynth11 ctx psi = do
  guesses <- liftIO $ runSynth1 ctx psi 1
  case guesses of
    [] -> deadend "runSynth11 unable to synth"
    [Guess x history _ _] -> addHistory "runSynth11" history $ pure x
