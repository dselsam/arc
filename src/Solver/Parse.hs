-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Solver.Parse where

import Util.Imports
import qualified Util.List as List
import qualified Util.Set as Set
import qualified Data.Set as Set
import Synth.Ex (Ex, ForTrain, ForTest)
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Shape as Shape
import Lib.Color
import Search.DFS
import Lib.Blank
import Lib.Grid (Grid)
import qualified Solver.Goal as Goal
import Lib.Dims
import qualified Lib.Parse
import qualified Lib.AlignShapes
import qualified Search.History as History
import qualified Search.Guess as Guess
import Search.Guess (Guess(Guess))
import Lib.AlignShapes (alignShapes)
import Solver.SolveM
import Synth1.Basic
import Synth.LazyFeatures
import Lib.Shape (Shape)
import qualified Data.Map as Map
import Solver.Goal (StdGoal, Goal(Goal))

getParse :: Lib.Parse.Options -> Grid Color -> SolveM [Shape Color]
getParse opts g = do
  -- TODO: have SearchT auto-lift MonadState and MonadReader?
  cache <- parseCache <$> lift get
  case Map.lookup (g, opts) cache of
    Nothing -> do
      let scene = Lib.Parse.parseScene g opts
      lift $ modify $ \s -> s { parseCache = Map.insert (g, opts) scene cache }
      pure scene
    Just scene -> pure scene

data ParseResult = ParseResult {
  inputs  :: Ex [Shape Color],
  outputs :: ForTrain [Shape Color]
  } deriving (Eq, Ord, Show)

getParseResult :: Lib.Parse.Options -> StdGoal -> SolveM ParseResult
getParseResult opts (Goal inputs outputs _) =
  ParseResult <$> (Ex.mapM (getParse opts) inputs) <*> (mapM (getParse opts) outputs)

enumParses :: StdGoal -> [Lib.Parse.Options] -> SolveM ParseResult
enumParses goal opts = do
    opts    <- oneOf "enumParses" $ map (\opt -> (show opt, opt)) opts
    inputs  <- Ex.mapM (getParse opts) (Goal.inputs goal)
    guard $ Ex.all (not . null) inputs
    outputs <- mapM (getParse opts) (Goal.outputs goal)
    pure $ ParseResult inputs outputs

enumUniqueParses :: StdGoal -> [Lib.Parse.Options] -> SolveM ParseResult
enumUniqueParses goal opts = do
  parses :: [Guess ParseResult] <- lift . enumAllG $ enumParses goal opts
  let uniqueParses  :: [Guess ParseResult] = List.stableUniqKey Guess.value parses
  oneOf "enumUniqueParses" $ map (\g -> (History.showCondensed (Guess.history g), Guess.value g)) uniqueParses

enumAlignments :: ForTrain [Shape Color] -> ForTrain [Shape Color] -> [Lib.AlignShapes.Options] -> SolveM (ForTrain [Maybe (Shape Color)])
enumAlignments inShapes outShapes opts = do
  opts             <- oneOf "enumAlignments" $ map (\opt -> (show opt, opt)) opts
  alignedOutShapes <- liftO $ flip mapM (zip inShapes outShapes) $ uncurry (alignShapes opts)
  pure $ alignedOutShapes

enumUniqueAlignments :: ForTrain [Shape Color] -> ForTrain [Shape Color] -> [Lib.AlignShapes.Options] -> SolveM (ForTrain [Maybe (Shape Color)])
enumUniqueAlignments inShapes outShapes opts = do
  alignments <- lift . enumAllG $ enumAlignments inShapes outShapes opts
  let uniqueAlignments = List.stableUniqKey Guess.value alignments
  oneOf "enumUniqueAlignments" $ map (\g -> (History.showCondensed (Guess.history g), Guess.value g)) uniqueAlignments

getBasicIntParseFeatures :: Ex (Grid Color) -> LazyFeatures CoreM Int
getBasicIntParseFeatures inputs = LazyFeatures $ choice "getBasicIntParseFeatures" [
  -- TODO: this is just enough to get 239be575
  ("nShapesContaining", do
      opts <- oneOf "parseOptions" [
        ("localColor", Lib.Parse.Options { Lib.Parse.kind = Lib.Parse.ParseLocalAny, Lib.Parse.color = Lib.Parse.ParseNoBlanksByColor }),
        ("localAny",   Lib.Parse.Options { Lib.Parse.kind = Lib.Parse.ParseLocalAny, Lib.Parse.color = Lib.Parse.ParseNoBlanksAny })
        ]
      pInputs <- Ex.mapM (getParse opts) inputs
      let colors = Ex.map (Grid.distinctVals nonBlank) inputs
      c <- oneOf "color" $ map (\c -> (show c, c)) $ Set.toList $ Set.intersectMany (Ex.toBigList colors)
      pure $ Ex.map (length . filter (Shape.containsVal c)) pInputs)
  ]
