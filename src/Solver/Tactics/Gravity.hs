-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleContexts #-}
module Solver.Tactics.Gravity where

import Util.Imports
import qualified Util.List as List
import qualified Data.List as List
import Solver.SolveM
import qualified Solver.Goal
import Search.SearchT
import Synth.Spec
import Synth.Basic
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Index as Index
import qualified Lib.Rect as Rect
import qualified Data.Map as Map
import qualified Util.Map as Map
import Data.Maybe (maybeToList)
import Lib.Axis
import Lib.Index (Index(Index))
import Synth1.Basic
import Synth.Core
import Synth.Bool

import qualified Synth.ExInfo as ExInfo
import Lib.Direction (Direction(..))
import qualified Lib.Direction as Direction
import Search.Guess (Guess(Guess))
import qualified Search.Guess as Guess
import Search.History (History)
import qualified Search.History as History
import Lib.Grid (Grid)
import Lib.Dims (Dims (Dims))
import Lib.Rect (Rect (Rect))
import qualified Lib.Dims as Dims
import qualified Data.Set as Set
import Solver.TacticResult (TacticResult(Decompose), Reconstruct, StdReconstruct)
import qualified Solver.TacticResult as TacticResult
import Lib.Color
import qualified Data.Maybe as Maybe
import Lib.Blank
import Lib.Motion (Motion(Motion), Trail(..))
import qualified Lib.Motion as Motion
import Solver.ArcContext
import qualified Solver.ArcContext as ArcContext
import Solver.Synth1Context
import Search.DFS
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import qualified Lib.Parse as Parse
import qualified Lib.AlignShapes as AlignShapes
import Solver.Parse
import Synth1.Basic
import qualified Solver.Tactics.Blast.Goal as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import Solver.Tactics.Blast.Mask (Mask(Mask))
import qualified Solver.Tactics.Blast.Mask as Mask
import Solver.Tactics.Blast.Candidate (Candidate(Candidate))
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Solver.Tactics.DyeInputs (synthG2C)
import Solver.Goal (Goal(Goal), StdGoal)
import Synth.EagerFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import Synth.LazyFeatures
import Synth.Spec
import Synth.Ints2Int
import Synth.Core
import Synth.Spec.ESpec (ESpec(ESpec))
import Synth.Spec.DSpec (DSpec(DSpec))
import qualified Synth.Spec.DSpec as DSpec
import qualified Synth.Spec.ESpec as ESpec
import Lib.Features
import Debug.Trace

data Gravity = Keep | Drop | Move Axis Direction deriving (Eq, Show, Ord)

-- gravityCouldExplain :: Grid Color -> [Shape Color] -> Grid Color -> CoreM [Gravity] -- weak version first that does no backwards analysis

isGravityKeep grav = case grav of
  Keep -> True
  _    -> False

isGravityMove grav = case grav of
  Move _ _ -> True
  _      -> False

applyShapeGravityStep :: Grid Color -> Shape Color -> Gravity -> Shape Color
applyShapeGravityStep grid shape grav =
  case grav of
    Keep -> shape
    Drop -> Shape.fill blank shape
    Move ax dir ->
      let candidate = Shape.move shape 1 ax dir in
          if flip any (Shape.indices candidate) $ \idx ->
                (not $ Dims.inBounds (Grid.dims grid) idx)
          then shape
          else candidate

iterateMaybe f = \x -> x:(List.unfoldr (fmap (\s -> (s,s)) . f) $ x)

applyGravity :: Grid Color -> [Shape Color] -> [Gravity] -> Grid Color
applyGravity grid shapes gravs =
  let keepMask = updateKeepMask (Grid.const (Grid.dims grid) False) shapes gravs in
    (\(x,_,_,_) -> x) . last $ iterateMaybe (List.uncurry4 applyGravityStep) (grid, shapes, gravs, keepMask)

-- applies one timestep of gravity, returning Nothing if no further motion is possible
applyGravityStep :: Grid Color -> [Shape Color] -> [Gravity] -> Grid Bool -> Maybe ((Grid Color, [Shape Color], [Gravity], Grid Bool))
applyGravityStep grid shapes gravs keepMask = do
  guard $ isJust $ List.find isGravityMove gravs
  (newGravs, newKeepMask) <- pure $ determineNewKeeps grid shapes gravs keepMask
  newShapes <- pure $ flip map (zip shapes newGravs) $ uncurry (applyShapeGravityStep grid)
  newGrid <- pure $ Grid.replacingShapes grid shapes newShapes
  pure (newGrid,newShapes,newGravs,newKeepMask)

determineNewKeeps :: Grid Color -> [Shape Color] -> [Gravity] -> Grid Bool -> ([Gravity], Grid Bool)
determineNewKeeps grid shapes gravs keepMask = (\(_,_,x,y) -> (x,y)) . last $ iterateMaybe (List.uncurry4 determineNewKeepsStep) (grid, shapes, gravs, keepMask)

 -- note, could use an iter instead of map to update the mask inside of this function
 -- would be cool if we could frame this in terms of deductive backprop
containsKeepPixel keepMask shape = any (Grid.get keepMask) $ Shape.indices shape

determineNewKeepsStep :: Grid Color -> [Shape Color] -> [Gravity] -> Grid Bool -> Maybe (Grid Color, [Shape Color], [Gravity], Grid Bool)
determineNewKeepsStep grid shapes gravs keepMask = do
  newGravs <- flip mapM (zip shapes gravs) $ \(shape, grav) -> (do
    if (grav == Drop || grav == Keep) then pure grav else do
      guard $ not $ containsKeepPixel keepMask shape -- check that we are not in conflict with the keepMask
      let shiftedShape = applyShapeGravityStep grid shape grav
      guard $ not $ containsKeepPixel keepMask shiftedShape -- check that the shifted shape is not in conflict with the keepMask
      guard $ Shape.upperLeft shiftedShape /= Shape.upperLeft shape -- check that we are not against an edge
      pure grav -- OK to move, return grav
    ) <|> pure Keep
  guard . not $ gravs == newGravs
  newKeepMask <- pure $ updateKeepMask keepMask shapes newGravs
  pure (grid, shapes, newGravs, newKeepMask)

updateKeepMask :: Grid Bool -> [Shape Color] -> [Gravity] -> Grid Bool
updateKeepMask keepMask shapes gravs =
  List.iter (zip shapes gravs) keepMask $ \acc (shape, grav) ->
    case grav of
      Keep -> pure $ List.iter (Shape.indices shape) acc $ \acc2 idx ->
        pure $ Grid.set acc2 True idx -- not sure if this is efficient
      _ -> pure acc

enumOrthoGravities :: SolveM Gravity
enumOrthoGravities = oneOf "enumOrthoGravities" $ (\x -> (show x, x)) <$> (map (uncurry Move) $ do
  {ax <- [Horizontal, Vertical]; dir <- [Normal, Reverse]; pure (ax, dir)})

-- simple gravity tactic
gravity :: StdGoal -> SolveM TacticResult
gravity goal@(Goal inputs outputs ctx) = do
  choice "gravity"
    [
      ("enumOrthoGravities", do
          guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
          guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
            let inColorCounts = Grid.buildCounts nonBlank input
                outColorCounts = Grid.buildCounts nonBlank output
            in
              inColorCounts == outColorCounts -- conservation of mass

          parseOptions <- oneOf "parseOptions" [
            ("reasonable", [
                Parse.Options { Parse.kind = Parse.ParseLocalNone,  Parse.color = Parse.ParseNoBlanksByColor }
              , Parse.Options   { Parse.kind = Parse.ParseLocalAny, Parse.color = Parse.ParseNoBlanksByColor }
              , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }
              , Parse.Options   { Parse.kind = Parse.ParseLocalAny, Parse.color = Parse.ParseNoBlanksAny }
              , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksAny }
              ])
            ]
          ParseResult pInputs pOutputs <- enumUniqueParses goal parseOptions

          gravss <- do
            grav <- enumOrthoGravities
            flip Ex.mapM (Ex.zip pInputs $ Ex.replicate (Ex.getInfo inputs) grav) $ \(shapes, grav) ->
              pure $ List.replicate (length shapes) grav

          let gravitatedInputs = map (List.uncurry3 applyGravity) (List.zip3 (Ex.train inputs) (Ex.train pInputs) (Ex.train gravss))
          -- guard $ flip all (List.zip4 (Ex.train inputs) (Ex.train pInputs) (Ex.train gravss) outputs ) $ \(input, shapes, gravs, output) ->
          --   (applyGravity input shapes gravs) == output
          guard $ flip all (zip gravitatedInputs outputs) $ \(newInput, output) -> newInput == output

          let guesses = (List.uncurry3 applyGravity) <$> zip3 (Ex.test inputs) (Ex.test pInputs) (Ex.test gravss)

          guard $ -- if gravitation changes a test input, then ensure it changed a test input
            (flip any (zip guesses (Ex.test inputs)) $ \(newInput, input) ->
                Dims.any (Grid.dims input) $ \idx -> Grid.get input idx /= Grid.get newInput idx) <=
            (flip any (zip gravitatedInputs (Ex.train inputs)) $ \(newInput, input) ->
                Dims.any (Grid.dims input) $ \idx -> Grid.get input idx /= Grid.get newInput idx)

          pure $ TacticResult.Guess guesses
          )
    ]
