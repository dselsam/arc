-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.GlobalFeatures where

import Util.Imports
import qualified Util.List as List
import Util.List (uncurry4)
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Data.Foldable
import Data.Ratio
import Lib.Axis
import Solver.SolveM
import Solver.Synth1Context
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import Search.SearchT
import Search.Guess
import qualified Search.Entry as Entry
import qualified Search.History as History

import Lib.Axis (Axis(..))
import Lib.Direction (Direction(..))
import qualified Lib.Axis as Axis
import Synth1.Synth1Context
import Solver.Goal (Goal(..), StdGoal)
import qualified Solver.Goal as Goal
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Corner as Corner
import Lib.Index
import Lib.Shape (Shape)
import Lib.Rect (Rect)
import qualified Lib.Rect as Rect
import qualified Lib.Shape as Shape
import qualified Lib.Axis as Axis
import qualified Lib.Dims as Dims
import qualified Lib.Grid as Grid
import qualified Lib.Line as Line
import qualified Lib.Dims as Dims
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.HasElems
import Solver.Tactics.Blast.Util
import Data.Maybe (listToMaybe, isJust, fromJust)

import qualified Util.List as List



----------- Start Mask Definitions -------------

allMask :: StdGoal -> Synth1M (Ex (Grid Bool))
allMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \gc -> Grid.const (Grid.dims gc) True

blankMask :: StdGoal -> Synth1M (Ex (Grid Bool))
blankMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \gc -> Grid.map (\_ val -> isBlank val) gc

onEdgeMask :: StdGoal -> Synth1M (Ex (Grid Bool))
onEdgeMask goal@(Goal inputs outputs ctx) =
  pure $ flip Ex.map inputs $ \ig ->
           Grid.map (\idx _ -> Dims.onEdge (Grid.dims ig) idx) ig

-- we could do this faster by just having a false grid and setting corners to true
isCornerMask :: StdGoal -> Synth1M (Ex (Grid Bool))
isCornerMask goal@(Goal inputs outputs ctx) =
  pure $ flip Ex.map inputs $ \ig ->
           Grid.map (\idx _ -> Corner.isCorner (Grid.dims ig) idx) ig


isSurroundedMask :: StdGoal -> Synth1M (Ex (Grid Bool))
isSurroundedMask goal@(Goal inputs outputs ctx) =
  pure $ flip Ex.map inputs $ \ig ->
           Grid.isSurrounded ig


axesBlank :: StdGoal -> Synth1M (Ex (Grid Bool))
axesBlank goal@(Goal inputs outputs ctx) = do
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        pure $ Map.insert ax (flip Ex.map inputs $ \ig -> Grid.axisBlank ig ax) acc
  axes <- enumVals
  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  pure $ reduceMasksAnd axMasks


-- NonBlank means it has at least one non-blank, not that the whole axis is nonblank
-- We need this because not (axesBlank ortho) = not (blank vertical) OR not (blank horizontal)
-- and not (blank vertical) OR not (blank horizontal) is different from not (blank vertical) AND not (blank horizontal)
axesNonBlank :: StdGoal -> Synth1M (Ex (Grid Bool))
axesNonBlank goal@(Goal inputs outputs ctx) = do
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        pure $ Map.insert ax (flip Ex.map inputs (\ig ->
          -- true for any axis that is not blank
          Grid.map (\_ b -> not b) (Grid.axisBlank ig ax))) acc
  axes <- enumVals
  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  pure $ reduceMasksAnd axMasks


axesHaveVal :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
axesHaveVal goal@(Goal inputs outputs ctx) cs = do
  -- one mask per Axis
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        pure $ Map.insert ax (flip Ex.map (Ex.zip inputs cs) (\(ig, c) -> Grid.axHasVal ig c ax)) acc
  axes <- enumVals
  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  combinedAxMasks <- oneOf "axesHaveVal.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks


nonBlankExistsToAxDirs :: StdGoal -> Synth1M (Ex (Grid Bool))
nonBlankExistsToAxDirs goal@(Goal inputs outputs ctx) = do
  let allAxDirMasks :: Map (Axis, Direction) (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc (ax, dir) ->
        pure $ Map.insert (ax, dir) (flip Ex.map inputs (\ig -> Grid.nonBlankExistsToAxDir ig ax dir)) acc
  (axDirs :: [(Axis, Direction)]) <- enumVals
  (axDirMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axDirs $ \axDir -> Map.lookup axDir allAxDirMasks
  combinedAxDirMasks <- oneOf "nonBlankExistsToAxDirs.binOp"
    [("and", reduceMasksAnd axDirMasks), ("or", reduceMasksOr axDirMasks)]
  pure combinedAxDirMasks


nonBlankLineExistsInAxDir :: StdGoal -> Synth1M (Ex (Grid Bool))
nonBlankLineExistsInAxDir goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.nonBlankLineExistsInAxDir ig ax dir

lineWithValExistsInAxDir :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
lineWithValExistsInAxDir goal@(Goal inputs outputs ctx) cs = do
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map (Ex.zip inputs cs) $ \(ig, c) -> Grid.lineWithValExistsInAxDir ig c ax dir

valExistsToAxDirs :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
valExistsToAxDirs goal@(Goal inputs outputs ctx) cs = do
  let allAxDirMasks :: Map (Axis, Direction) (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc (ax, dir) ->
        pure $ Map.insert (ax, dir) (flip Ex.map (Ex.zip inputs cs) (\(ig, c) -> Grid.valExistsToAxDir ig c ax dir)) acc
  (axDirs :: [(Axis, Direction)]) <- enumVals
  (axDirMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axDirs $ \axDir -> Map.lookup axDir allAxDirMasks
  pure $ reduceMasksAnd axDirMasks


nearestValInAxDirsIsSame :: StdGoal -> Synth1M (Ex (Grid Bool))
nearestValInAxDirsIsSame goal@(Goal inputs outputs ctx) = do
  ((ax1, dir1) :: (Axis, Direction)) <- enumVals
  ((ax2, dir2) :: (Axis, Direction)) <- enumVals
  guard $ (ax1, dir1) /= (ax2, dir2)
  let allAxdir1Vals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax1 dir1
  let allAxdir2Vals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax2 dir2
  let sameVals :: Ex (Grid Bool) = flip Ex.map (Ex.zip allAxdir1Vals allAxdir2Vals) $ \(ax1vals, ax2vals) ->
        Grid.fromFunc (Grid.dims ax1vals) $ \idx -> if (Grid.get ax1vals idx) == (Grid.get ax2vals idx) then True else False
  pure sameVals


surroundedByValOnAxesMask :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
surroundedByValOnAxesMask goal@(Goal inputs outputs ctx) cs = do
  (axes :: [Axis]) <- enumVals
  -- Dirty exclusion of the "all" case to improve safety
  guard $ axes /= [Horizontal, Vertical, DownRight, DownLeft]

  -- one Ex per axis
  let axMasks :: [Ex (Grid Bool)] = flip map axes $ \ax ->
        let existsNormal = flip Ex.map (Ex.zip inputs cs) $ \(ig, c) -> Grid.valExistsToAxDir ig c ax Normal
            existsReverse = flip Ex.map (Ex.zip inputs cs) $ \(ig, c) -> Grid.valExistsToAxDir ig c ax Reverse in
          flip Ex.map (Ex.zip existsNormal existsReverse) $ \(norm, rev) -> Grid.mapBinOp (Blank.andD True) norm rev
  combinedAxMasks <- oneOf "surroundedByValOnAxes.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks


flankedByUniformOnAx :: StdGoal -> Synth1M (Ex (Grid Bool))
flankedByUniformOnAx goal@(Goal inputs outputs ctx) = do
  (axes :: [Axis]) <- enumVals
  -- Dirty exclusion of the "all" case to improve safety
  guard $ axes /= [Horizontal, Vertical, DownRight, DownLeft]

  -- one Ex per axis
  let axMasks :: [Ex (Grid Bool)] = flip map axes $ \ax ->
        let reverseVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Reverse
            normalVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Normal in
        (flip Ex.map (Ex.zip3 inputs reverseVals normalVals) $ \(ig, rVals, nVals) ->
            flip Grid.map ig $ \idx x ->
            -- a stricter guard than x /= (Grid.get rVals idx) would be isBlank x
            if (Grid.get rVals idx) == (Grid.get nVals idx) &&
            nonBlank (Grid.get rVals idx) && x /= (Grid.get rVals idx) then True
            else False)
  combinedAxMasks <- oneOf "flankedByUniformOnAx.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks


flankedByComboOnAxMask :: StdGoal -> Synth1M (Ex (Grid Bool))
flankedByComboOnAxMask goal@(Goal inputs outputs ctx) = do
  c1s <- Grid.enumRelevantColors inputs outputs
  c2s <- Grid.enumRelevantColors inputs outputs
  (axes :: [Axis]) <- enumVals
  -- Dirty exclusion of the "all" case to improve safety
  guard $ axes /= [Horizontal, Vertical, DownRight, DownLeft]
  -- one Ex per axis
  let axMasks :: [Ex (Grid Bool)] = flip map axes $ \ax ->
        let reverseVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Reverse
            normalVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Normal in
        (flip Ex.map (Ex.zip4 reverseVals normalVals c1s c2s) $ \(rVals, nVals, c1, c2) ->
            flip Grid.map rVals $ \idx revX ->
             if revX == c1 then (Grid.get nVals idx) == c2
             else if revX == c2 then (Grid.get nVals idx) == c1
             else False)
  combinedAxMasks <- oneOf "flankedByUniformOnAx.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks


getIntersectionMask :: StdGoal -> Synth1M (Ex (Grid Bool))
getIntersectionMask goal@(Goal inputs outputs ctx) = do
  (axes :: [Axis]) <- enumVals
  guard $ (length axes) > 1

  -- one Ex per axis
  let axMasks :: [Ex (Grid Bool)] = flip map axes $ \ax ->
        let reverseVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Reverse
            normalVals = flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax Normal in
        (flip Ex.map (Ex.zip3 inputs reverseVals normalVals) $ \(ig, rVals, nVals) ->
            flip Grid.map ig $ \idx x ->
            -- a stricter guard than x /= (Grid.get rVals idx) would be isBlank x
            if (Grid.get rVals idx) == (Grid.get nVals idx) &&
            nonBlank (Grid.get rVals idx) && x /= (Grid.get rVals idx) then True
            else False)
  pure $ reduceMasksAnd axMasks


flankedBySpecialOnAx :: StdGoal -> Synth1M (Ex (Grid Bool))
flankedBySpecialOnAx goal@(Goal inputs outputs ctx) = do
  (axes :: [Axis]) <- enumVals
  -- Dirty exclusion of the "all" case to improve safety
  guard $ axes /= [Horizontal, Vertical, DownRight, DownLeft]
  idxLists <- oneOf "ctx.idxLists" (ctxIdxLists ctx)
  -- one Ex per axis
  let axMasks :: [Ex (Grid Bool)] = flip map axes $ \ax ->
        let reverseVals = flip Ex.map inputs $ \ig -> Grid.idxOfNearestInAxDir ig ax Reverse
            normalVals = flip Ex.map inputs $ \ig -> Grid.idxOfNearestInAxDir ig ax Normal in
        (flip Ex.map (Ex.zip4 inputs reverseVals normalVals idxLists) $ \(ig, rVals, nVals, idxs) ->
            flip Grid.map ig $ \idx x ->
             if (isJust (Grid.get rVals idx) && elem (fromJust (Grid.get rVals idx)) idxs) &&
                (isJust (Grid.get nVals idx) && elem (fromJust (Grid.get nVals idx)) idxs)
             then True
            else False)
  combinedAxMasks <- oneOf "flankedByUniformOnAx.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks


isValMask :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
isValMask goal@(Goal inputs outputs ctx) cs =
  pure $ flip Ex.map (Ex.zip inputs cs) $ \(gc, c) ->
           Grid.map (\_ val -> val == c) gc


neighborIsVal :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Bool))
neighborIsVal goal@(Goal inputs outputs ctx) cs = do
  -- precompute
  let allAxDirMasks :: Map (Axis, Direction) (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc (ax, dir) ->
        pure $ Map.insert (ax, dir) (flip Ex.map (Ex.zip inputs cs) (\(ig, c) -> flip Grid.map ig $ \idx _ ->
        let idxInAxDir = Direction.step idx 1 ax dir in
          if Dims.inBounds (Grid.dims ig) idxInAxDir then (Grid.get ig idxInAxDir) == c
          else False)) acc

  (axDirs :: [(Axis, Direction)]) <- enumVals
  (axDirMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axDirs $ \axDir -> Map.lookup axDir allAxDirMasks
  -- Interpretation of OR: Is touching the val in any of axDirs
  combinedAxDirMasks <- oneOf "neighborIsVal.binOp"
    [("and", reduceMasksAnd axDirMasks), ("or", reduceMasksOr axDirMasks)]
  pure combinedAxDirMasks


idxInAnyAxMask :: StdGoal -> Synth1M (Ex (Grid Bool))
idxInAnyAxMask goal@(Goal inputs outputs ctx) = do
  idxs <- oneOf "ctx.idxs" (ctxIdxs ctx)
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        let axMask = flip Ex.map (Ex.zip inputs idxs) (\(ig, idx) -> Grid.idxInAxis ig idx ax) in
          pure $ Map.insert ax axMask acc
  (axes :: [Axis]) <- enumVals
  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  -- note how this is an OR
  -- interpretation: does this index exist in any of these axes?
  pure $ reduceMasksOr axMasks


idxInAxDirMask :: StdGoal -> Synth1M (Ex (Grid Bool))
idxInAxDirMask goal@(Goal inputs outputs ctx) = do
  idxs <- oneOf "ctx.idxs" (ctxIdxs ctx)
  (ax :: Axis) <- enumVals
  (dir :: Direction) <- enumVals
  pure $ flip Ex.map (Ex.zip inputs idxs) $ \(ig, idx) -> Grid.idxInAxDir ig idx ax dir


surroundedBySpecialOnAxesMask :: StdGoal -> Synth1M (Ex (Grid Bool))
surroundedBySpecialOnAxesMask goal@(Goal inputs outputs ctx) = do
  idxLists <- oneOf "ctx.idxLists" (ctxIdxLists ctx)
  guard $ flip Ex.all idxLists $ \idxs -> not (null idxs)
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        let anyInNorm = flip Ex.map (Ex.zip inputs idxLists) $ \(ig, idxs) -> Grid.anyIdxInAxDir ig idxs ax Normal
            anyInRev = flip Ex.map (Ex.zip inputs idxLists) $ \(ig, idxs) -> Grid.anyIdxInAxDir ig idxs ax Reverse
            axMasks = flip Ex.map (Ex.zip anyInNorm anyInRev) $ \(norm, rev) -> Grid.mapBinOp (Blank.andD True) norm rev in
          pure $ Map.insert ax axMasks acc

  (axes :: [Axis]) <- enumVals
  -- Dirty exclusion of the "all" case to improve safety
  guard $ axes /= [Horizontal, Vertical, DownRight, DownLeft]

  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  combinedAxMasks <- oneOf "surroundedByValOnAxes.binOp" [("and", reduceMasksAnd axMasks), ("or", reduceMasksOr axMasks)]
  pure combinedAxMasks




anyIdxInAnyAxMask :: StdGoal -> Synth1M (Ex (Grid Bool))
anyIdxInAnyAxMask goal@(Goal inputs outputs ctx) = do
  idxLists <- oneOf "ctx.idxLists" (ctxIdxLists ctx)
  guard $ flip Ex.all idxLists $ \idxs -> not (null idxs)
  -- each grid bool represents whether or not an index has any of the associated idxs in its ax
  let allAxMasks :: Map Axis (Ex (Grid Bool)) = List.iter elems Map.empty $ \acc ax ->
        let axMask = flip Ex.map (Ex.zip inputs idxLists) $ \(ig, idxs) ->
              List.reduce (\g1 g2 -> Grid.mapBinOp (Blank.orD True) g1 g2) (\idx -> Grid.idxInAxis ig idx ax) idxs in
          pure $ Map.insert ax axMask acc
  (axes :: [Axis]) <- enumVals
  (axMasks :: [Ex (Grid Bool)]) <- liftO $ flip mapM axes $ \ax -> Map.lookup ax allAxMasks
  -- note the OR: do any of the indices exist in any of the axes?
  pure $ reduceMasksOr axMasks


containedInShapeMask :: StdGoal -> Synth1M (Ex (Grid Bool))
containedInShapeMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Shape.indices s) $ \idx -> (idx, True)

touchingShapeOrthoMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingShapeOrthoMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapeOrthoNeighbors ig s) $ \idx -> (idx, True)

touchingShapeDiagMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingShapeDiagMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapeDiagNeighbors ig s) $ \idx -> (idx, True)

touchingShapeAllMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingShapeAllMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapeAllNeighbors ig s) $ \idx -> (idx, True)

touchingAnyShapeOrthoMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingAnyShapeOrthoMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  pure $ flip Ex.map (Ex.zip inputs shapeLists) $  \(ig, shapes) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapesNeighbors ig shapes Grid.shapeOrthoNeighbors) $ \idx -> (idx, True)

touchingAnyShapeDiagMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingAnyShapeDiagMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  pure $ flip Ex.map (Ex.zip inputs shapeLists) $  \(ig, shapes) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapesNeighbors ig shapes Grid.shapeDiagNeighbors) $ \idx -> (idx, True)


touchingAnyShapeAllMask :: StdGoal -> Synth1M (Ex (Grid Bool))
touchingAnyShapeAllMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  pure $ flip Ex.map (Ex.zip inputs shapeLists) $  \(ig, shapes) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map (Grid.shapesNeighbors ig shapes Grid.shapeAllNeighbors) $ \idx -> (idx, True)

containedInAnyShapeMask :: StdGoal -> Synth1M (Ex (Grid Bool))
containedInAnyShapeMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  pure $ flip Ex.map (Ex.zip inputs shapeLists) $ \(ig, shapes) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      List.iter shapes falseGrid (\accGrid shape -> pure $ Grid.setPairs accGrid $ flip Prelude.map (Shape.indices shape) $ \idx -> (idx, True))

containedInShapeEnclosingRectMask :: StdGoal -> Synth1M (Ex (Grid Bool))
containedInShapeEnclosingRectMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) ->
    let falseGrid = Grid.const (Grid.dims ig) False
        sRect = Shape.enclosingRect s in
      Grid.setPairs falseGrid $ flip Prelude.map (Rect.getIdxs sRect) $ \idx -> (idx, True)

containedInAnyShapeEnclosingRectMask :: StdGoal -> Synth1M (Ex (Grid Bool))
containedInAnyShapeEnclosingRectMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  let finalMask = flip Ex.map (Ex.zip inputs shapeLists) $ \(ig, shapes) ->
        let falseGrid = Grid.const (Grid.dims ig) False in
          List.iter shapes falseGrid (\accGrid shape -> pure $ Grid.setPairs accGrid $ flip Prelude.map (Rect.getIdxs (Shape.enclosingRect shape)) $ \idx -> (idx, True))
  pure finalMask


containedInIdxListMask :: StdGoal -> Synth1M (Ex (Grid Bool))
containedInIdxListMask goal@(Goal inputs outputs ctx) = do
  idxLists <- oneOf "ctx.idxLists" (ctxIdxLists ctx)
  guard $ flip Ex.all idxLists $ \idxs -> not (null idxs)
  pure $ flip Ex.map (Ex.zip inputs idxLists) $ \(ig, idxs) ->
    let falseGrid = Grid.const (Grid.dims ig) False in
      Grid.setPairs falseGrid $ flip Prelude.map idxs $ \idx -> (idx, True)

isIdxMask :: StdGoal -> Synth1M (Ex (Grid Bool))
isIdxMask goal@(Goal inputs outputs ctx) = do
  idxs <- oneOf "ctx.idxs" (ctxIdxs ctx)
  pure $ flip Ex.map (Ex.zip inputs idxs) $ \(ig, idx) -> Grid.fromFunc (Grid.dims ig) $ \ffIdx ->
    if ffIdx == idx then True else False
    -- alternative:
    --let falseGrid = Grid.const (Grid.dims ig) False in
      --Grid.set falseGrid True idx




-- INT FEATURES (part of masks)
-- note the suffix -Mask here refers to something that will be turned into a mask.
-- in other words, the mask is determined by the integer value, so we stick with the naming convention

rowMask :: StdGoal -> Synth1M (Ex (Grid Int))
rowMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> row) g

colMask :: StdGoal -> Synth1M (Ex (Grid Int))
colMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> col) g

downRightIdMask :: StdGoal -> Synth1M (Ex (Grid Int))
downRightIdMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\idx _ -> Line.idxAxisId (Grid.dims g) DownRight idx) g

downLeftIdMask :: StdGoal -> Synth1M (Ex (Grid Int))
downLeftIdMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\idx _ -> Line.idxAxisId (Grid.dims g) DownLeft idx) g

diffMask :: StdGoal -> Synth1M (Ex (Grid Int))
diffMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> row - col) g

sumMask :: StdGoal -> Synth1M (Ex (Grid Int))
sumMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> row + col) g

maxMask :: StdGoal -> Synth1M (Ex (Grid Int))
maxMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> max row col) g

minMask :: StdGoal -> Synth1M (Ex (Grid Int))
minMask goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \g -> Grid.map (\(Index row col) _ -> min row col) g


nInAxisMask :: StdGoal -> Synth1M (Ex (Grid Int))
nInAxisMask goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.nInAxis ig ax

nBlankInAxisMask :: StdGoal -> Synth1M (Ex (Grid Int))
nBlankInAxisMask goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.nBlankInAxis ig ax


nDistinctInAxisMask :: StdGoal -> Synth1M (Ex (Grid Int))
nDistinctInAxisMask goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.nDistinctInAxis ig ax


nNeighborsMask :: StdGoal -> Synth1M (Ex (Grid Int))
nNeighborsMask goal@(Goal inputs outputs ctx) = do
  -- FIXME (perf): Can precompute, and then sum
  (axDirs :: [(Axis, Direction)]) <- enumVals
  pure $ flip Ex.map inputs $ \g -> Grid.map (\idx _ -> Grid.nNeighborsAxDirs g axDirs idx) g

nNeighborColorsMask :: StdGoal -> Synth1M (Ex (Grid Int))
nNeighborColorsMask goal@(Goal inputs outputs ctx) = do
  -- FIXME (perf): Can precompute, and then sum
  (axDirs :: [(Axis, Direction)]) <- enumVals
  pure $ flip Ex.map inputs $ \g -> Grid.map (\idx _ -> Grid.nNeighborColorsAxDirs g axDirs idx) g


minDistToShapeMask :: StdGoal -> Synth1M (Ex (Grid Int))
minDistToShapeMask goal@(Goal inputs outputs ctx) = do
  (shapes :: Ex (Shape Color)) <- oneOf "ctx.shapes" (ctxShapes ctx)
  guard $ Ex.all (\s -> not (Shape.null s)) shapes
  pure $ flip Ex.map (Ex.zip inputs shapes) $ \(ig, s) -> Grid.map (\idx val ->
    fromJust (Shape.minDistToIdx DiagDist idx s)) ig

minDistToAnyShapeMask :: StdGoal -> Synth1M (Ex (Grid Int))
minDistToAnyShapeMask goal@(Goal inputs outputs ctx) = do
  (shapeLists :: Ex ([Shape Color])) <- oneOf "ctx.shapeLists" (ctxShapeLists ctx)
  pure $ flip Ex.map (Ex.zip inputs shapeLists) $ \(ig, shapes) ->
    let allShapeIdxs :: [Index] = nub $ List.iter shapes [] $ \acc s -> pure (acc ++ (Shape.indices s)) in
      flip Grid.map ig (\idx val -> minimum (flip Prelude.map allShapeIdxs (\sIdx -> Axis.dist DiagDist sIdx idx)))


-- MAYBE INT FEATURES (part of masks)

distToNearestNonBlankInAxDirMask :: StdGoal -> Synth1M (Ex (Grid (Maybe Int)))
distToNearestNonBlankInAxDirMask goal@(Goal inputs outputs ctx) = do
  -- FIXME: should this sample dirs (just the dirs) and take the minimum? ( we are now doing this, but shold it stay?)
  -- FIXME: should the edge be considered a blank? It currently isn't
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map inputs $ \g -> Grid.distToNearestNonBlankInAxDir g ax dir


distToNearestValInAxDirMask :: StdGoal -> Synth1M (Ex (Grid (Maybe Int)))
distToNearestValInAxDirMask goal@(Goal inputs outputs ctx) = do
  cs <- Grid.enumRelevantColors inputs outputs
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map (Ex.zip inputs cs) $ \(ig, c) -> Grid.distToNearestValInAxDir ig c ax dir


distToNearestBlankInAxDirMask :: StdGoal -> Synth1M (Ex (Grid (Maybe Int)))
distToNearestBlankInAxDirMask goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  --dir <- enumVals
  --pure $ flip Ex.map inputs $ \g -> (Grid.distToNearestBlankInAxDir g ax dir))
  (dirs :: [Direction]) <- enumVals
  let dirMaps :: [Ex (Grid (Maybe Int))] = flip map dirs $ \dir ->
       flip Ex.map inputs $ \g -> (Grid.distToNearestBlankInAxDir g ax dir)
  -- again, wouldn't have to do any of this if we treated edges as blanks
  -- motivating checksum: 3bdb
  -- we also wouldn't need this if we put distances to non/blanks in axis. Check if it would lead to bad guesses
  let reducedDirMap :: Ex (Grid (Maybe Int)) = List.reduce (\ex1 ex2 ->
       flip Ex.map (Ex.zip ex1 ex2) (\(mbG1, mbG2) -> flip Grid.map mbG1 (\idx mbVal ->
         if isJust mbVal && isJust (Grid.get mbG2 idx) then
           Just (min (fromJust mbVal) (fromJust (Grid.get mbG2 idx)))
         else if isJust (Grid.get mbG2 idx) then Grid.get mbG2 idx
         else mbVal))) id dirMaps
  pure reducedDirMap

----------- End Mask Definitions -------------


----------- Start Candidate Definitions -------------

-- would be a bit better as a Maybe Color?
neighborVal :: StdGoal -> Synth1M (Ex (Grid Color))
neighborVal goal@(Goal inputs outputs ctx) = do
  ((ax, dir) :: (Axis, Direction)) <- enumVals
  pure $ flip Ex.map inputs $ \input -> flip Grid.map input $ \idx val ->
    -- note use of Grid.getD
    Grid.getD input (Direction.step idx 1 ax dir)


blankCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
blankCandidate goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \gc -> Grid.const (Grid.dims gc) blank

constCandidate :: StdGoal -> Ex Color -> Synth1M (Ex (Grid Color))
constCandidate goal@(Goal inputs outputs ctx) cs = pure $ flip Ex.map (Ex.zip inputs cs) $ \(gc, c) -> Grid.const (Grid.dims gc) c

axMaxCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
axMaxCandidate goal@(Goal inputs outputs ctx) =  do
  ax <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.axMax ig ax

nearestNonBlankCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
nearestNonBlankCandidate goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \ig -> Grid.nearestNonBlank ig

nearestNonSelfValCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
nearestNonSelfValCandidate goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \ig -> Grid.nearestNonSelfVal ig

nearestNonSelfIdxCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
nearestNonSelfIdxCandidate goal@(Goal inputs outputs ctx) = pure $ flip Ex.map inputs $ \ig -> Grid.nearestNonSelfIdx ig


nearestValInAxDirCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
nearestValInAxDirCandidate goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.nearestValInAxDir ig ax dir

furthestValInAxDirCandidate :: StdGoal -> Synth1M (Ex (Grid Color))
furthestValInAxDirCandidate goal@(Goal inputs outputs ctx) = do
  ax <- enumVals
  dir <- enumVals
  pure $ flip Ex.map inputs $ \ig -> Grid.furthestValInAxDir ig ax dir


----------- End Candidate Definitions -------------




--The below are compiled and maintained for MonsterBlast
enumIndex2Int :: StdGoal -> Synth1M (Ex (Grid Int))
enumIndex2Int goal@(Goal inputs outputs ctx) = do
  choice "index2int" [
    ("row", rowMask goal)
    , ("col", colMask goal)
    , ("downRightId", downRightIdMask goal)
    , ("downLeftId", downLeftIdMask goal)
    , ("sum", sumMask goal)
    , ("diff", diffMask goal)
    , ("max",  maxMask goal)
    , ("min",  minMask goal)
    , ("nInAxis", nInAxisMask goal)
    , ("nBlankInAxis", nBlankInAxisMask goal)
    , ("nDistinctInAxis", nDistinctInAxisMask goal)
    , ("nNeighbors", nNeighborsMask goal)
    , ("extremeDistToNonBlank", Grid.extremeNonBlankDistances inputs)
    , ("extremeDistanceToBlank", Grid.extremeBlankDistances inputs)
    , ("nNeighborColors", nNeighborColorsMask goal)
    , ("minDistToShape", minDistToShapeMask goal)
    , ("minDistToAnyShape", minDistToAnyShapeMask goal)
    ]



enumIndex2MaybeInt :: StdGoal -> Synth1M (Ex (Grid (Maybe Int)))
enumIndex2MaybeInt goal@(Goal inputs outputs ctx) = do
  choice "index2maybeInt" [
    ("distToNearestNonBlankInAxDir", do
      -- FIXME: should this sample axdirs, and take the minimum?
      ax <- enumVals
      dir <- enumVals
      pure $ flip Ex.map inputs $ \g -> (Grid.distToNearestNonBlankInAxDir g ax dir))
    , ("distToNearestBlankInAxDir", do
      -- FIXME: should this sample axdirs, and take the minimum?
      ax <- enumVals
      dir <- enumVals
      pure $ flip Ex.map inputs $ \g -> (Grid.distToNearestBlankInAxDir g ax dir))
    , ("distToNonBlankLineInAxDir", do
      -- FIXME: should this sample axdirs, and take the minimum?
      ax <- enumVals
      dir <- enumVals
      pure $ flip Ex.map inputs $ \g -> (Grid.distToNonBlankLineInAxDir g ax dir))
    -- note this is only in monster blast, not even in ray blast currently
    , ("extremeDistToVal", do
      cs <- Grid.enumRelevantColors inputs outputs
      Grid.extremeDistancesToVal inputs cs)
    , ("distToNearestValInAxDir", distToNearestValInAxDirMask goal)
    ]
