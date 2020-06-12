{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.ShapeFeaturesBlast where

import qualified Data.Maybe as Maybe
import Data.Maybe (listToMaybe, isJust, fromJust)
import Debug.Trace
import Util.Imports
import qualified Search.History as History
import Util.List as List
import Data.List hiding (partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Synth1.Basic
import Search.SearchT
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Solver.Tactics.Blast.Goal (Goal(..))
import Solver.Tactics.Blast.Mask (Mask(..))
import Solver.Tactics.Blast.Candidate (Candidate(..))
import Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.Features
import Solver.Tactics.Blast.ReconstructBuilders
import qualified Solver.Tactics.Blast.Blast as Blast
import Solver.Tactics.Blast.DecisionList (greedyDecisionList)
import qualified Solver.Tactics.Blast.Goal as Goal
import qualified Solver.Tactics.Blast.Mask as Mask
import qualified Solver.Tactics.Blast.Candidate as Candidate
import qualified Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.Features as Features
import Solver.TacticResult (TacticResult(..))
import qualified Solver.TacticResult as TacticResult

import qualified Search.History as History
import Lib.Blank
import Lib.Corner
import qualified Lib.Grid as Grid
import Solver.SolveM
import Solver.Goal (StdGoal)
import qualified Solver.Goal as TacGoal
import Solver.TacticResult (TacticResult)

import Solver.Synth1Context
import qualified Lib.Axis as Axis
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Color
import qualified Lib.Dims as Dims
import Lib.Rect
import qualified Lib.Rect as Rect
import qualified Lib.Parse as Parse
import Lib.Parse
import Lib.Index
import Lib.Features (rectHoles)
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.Util

import Solver.Tactics.Blast.Util

-- FIXME: Should really first compute the lists of the extremes, and then have "uniqueBiggestRect" for
-- example that checks if there is only one biggest rect. Else you give a list (in a different conditional)
buildShapeFeatureBlastCtx :: Ex (Grid Color) -> ForTrain (Grid Color) -> Synth1Context
buildShapeFeatureBlastCtx inputs outputs =
  Synth1Context (length outputs) (length (Ex.test inputs)) True
    (newInts ++ (ctxInts extremeShapeContext))
    (newColors ++ (ctxColors extremeShapeContext))
    (newIdxs ++ (ctxIdxs extremeShapeContext))
    (newIdxLists ++ (ctxIdxLists extremeShapeContext))
    (newShapes ++ (ctxShapes extremeShapeContext))
    (newShapeLists)
  where

    allNonBlankRows = Ex.map (\ig -> Grid.nonBlankRows ig) inputs
    allNonBlankCols = Ex.map (\ig -> Grid.nonBlankCols ig) inputs

    -- we could parameterize this by shape, and then just iter over all shape options to add them
    orthoColorParse :: Ex [Shape Color] = flip Ex.map inputs $ \(ig :: Grid Color) ->
        parseScene ig Parse.Options { Parse.kind = Parse.ParseLocalOrtho,   Parse.color = Parse.ParseNoBlanksByColor }

    closedShapes :: Ex [Shape Color] = flip Ex.map orthoColorParse $ \inputParse ->
        filter (\s -> (rectHoles s) == 0) inputParse

    oneHoleShapes :: Ex [Shape Color] = flip Ex.map orthoColorParse $ \inputParse ->
        filter (\s -> (rectHoles s) == 1) inputParse

    gt1HoleShapes :: Ex [Shape Color] = flip Ex.map orthoColorParse $ \inputParse ->
        filter (\s -> (rectHoles s) == 1) inputParse

    inputRects :: Ex [Shape Color] = flip Ex.map orthoColorParse $ \inputParse ->
        filter (\s -> Shape.isRect s) inputParse
    inputFilledRects :: Ex [Shape Color] = flip Ex.map inputRects $ \rs ->
        filter (\s -> Shape.isFilledRect s) rs
    -- motivated by ec88
    -- isRectOffEdge :: Dims -> Shape a -> Bool
    -- could also be named "partial rects"
    inputRectsOffGrid :: Ex [Shape Color] = flip Ex.map (Ex.zip inputs orthoColorParse) $ \(ig, inputParse) ->
        filter (\s -> Shape.isRectOffEdge (Grid.dims ig) s) inputParse
    inputSquares :: Ex [Shape Color] = flip Ex.map inputRects $ \rs ->
        filter (\r -> Rect.isSquare (Shape.enclosingRect r)) rs


    biggestShapeLists :: Ex (Maybe [Shape Color]) =
      if flip Ex.all orthoColorParse (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map orthoColorParse (\shapes -> List.argmaxesKey (\s -> Shape.nPoints s) shapes) in
          flip Ex.map allMaxes (\maxes -> Just maxes)
      else flip Ex.map orthoColorParse (\_ -> Nothing)

    smallestShapeLists :: Ex (Maybe [Shape Color]) =
      if flip Ex.all orthoColorParse (\shapes -> not (null shapes)) then
        let allMins = flip Ex.map orthoColorParse (\shapes -> List.argminsKey (\s -> Shape.nPoints s) shapes) in
          flip Ex.map allMins (\mins -> Just mins)
      else flip Ex.map orthoColorParse (\_ -> Nothing)

    -- note how we ensure that there is a UNIQUE biggest/smallest rectangle
    biggestShapes :: Ex (Maybe (Shape Color)) =
      if flip Ex.all orthoColorParse (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map orthoColorParse (\shapes -> List.argmaxesKey (\s -> Shape.nPoints s) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map inputRects (\_ -> Nothing)


    biggestClosedShapes :: Ex (Maybe (Shape Color)) =
      if flip Ex.all closedShapes (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map closedShapes (\shapes -> List.argmaxesKey (\s -> Shape.nPoints s) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map closedShapes (\_ -> Nothing)

    smallestClosedShapes :: Ex (Maybe (Shape Color)) =
      if flip Ex.all closedShapes (\shapes -> not (null shapes)) then
        let allMins = flip Ex.map closedShapes (\shapes -> List.argminsKey (\s -> Shape.nPoints s) shapes) in
          if flip Ex.all allMins (\mins -> length mins == 1) then
            flip Ex.map allMins (\mins -> Just (mins !! 0))
          else flip Ex.map allMins (\_ -> Nothing)
      else flip Ex.map closedShapes (\_ -> Nothing)


    biggestShapesByEnclosingRect :: Ex (Maybe (Shape Color)) =
      if flip Ex.all orthoColorParse (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map orthoColorParse (\shapes -> List.argmaxesKey (\s -> Rect.area (Shape.enclosingRect s)) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map inputRects (\_ -> Nothing)

    -- note that this is by area
    biggestRects :: Ex (Maybe (Shape Color)) =
      if flip Ex.all inputRects (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map inputRects (\shapes -> List.argmaxesKey (\s -> Rect.area (Shape.enclosingRect s)) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map inputRects (\_ -> Nothing)

    -- note that this is by area
    smallestRects :: Ex (Maybe (Shape Color)) =
      if flip Ex.all inputRects (\shapes -> not (null shapes)) then
        let allMins = flip Ex.map inputRects (\shapes -> List.argminsKey (\s -> Rect.area (Shape.enclosingRect s)) shapes) in
          if flip Ex.all allMins (\mins -> length mins == 1) then
            flip Ex.map allMins (\mins -> Just (mins !! 0))
          else flip Ex.map allMins (\_ -> Nothing)
      else flip Ex.map inputRects (\_ -> Nothing)

    -- note that this is by area. We aren't exactly consistent with this...
    biggestRectsOffGrid :: Ex (Maybe (Shape Color)) =
      if flip Ex.all inputRectsOffGrid (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map inputRectsOffGrid (\shapes -> List.argmaxesKey (\s -> Rect.area (Shape.enclosingRect s)) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map inputRectsOffGrid (\_ -> Nothing)

    biggestFilledRects :: Ex (Maybe (Shape Color)) =
      if flip Ex.all inputFilledRects (\shapes -> not (null shapes)) then
        let allMaxes = flip Ex.map inputFilledRects (\shapes -> List.argmaxesKey (\s -> Shape.nPoints s) shapes) in
          if flip Ex.all allMaxes (\maxes -> length maxes == 1) then
            flip Ex.map allMaxes (\maxes -> Just (maxes !! 0))
          else flip Ex.map allMaxes (\_ -> Nothing)
      else flip Ex.map inputFilledRects (\_ -> Nothing)

    nonBlankShapes :: Ex (Maybe (Shape Color)) = flip Ex.map inputs $ \ig -> Grid.nonBlankShape ig

    extremeShapeContext = List.iter
        [("biggestShapes", biggestShapes), ("biggestShapesByEnclosingRect", biggestShapesByEnclosingRect),
         ("smallestRects", smallestRects), ("biggestRects", biggestRects), ("biggestFilledRects", biggestFilledRects),
         ("biggestRectsOffGrid", biggestRectsOffGrid), ("nonBlankShape", nonBlankShapes),
         ("biggestClosedShape", biggestClosedShapes), ("smallestClosedShape", smallestClosedShapes)]
        (emptySynth1Context (length $ Ex.train inputs) (length $ Ex.test inputs)) $ \xShapeCtx (xShapeName, xShapes) ->
      if flip Ex.all xShapes (\xShape -> isJust xShape)
      then pure $ addShapeFeatures inputs xShapeName (Ex.map (\xShape -> fromJust xShape) xShapes) xShapeCtx
      else pure xShapeCtx

    newInts = []

    newIdxs = [] ++
      (if flip Ex.any inputs (\ig -> Grid.allBlank ig) then []
          else
          [
            -- add extreme idxs (e.g., highest, breaking ties by left/right

            -- top-most, break ties by left-most
            ("topLeft", flip Ex.map (Ex.zip inputs allNonBlankRows) $ \(ig, nonBlankRows) ->
                let minRow = minimum nonBlankRows
                    minColInMinRow = minimum $ filter (\col ->
                      nonBlank (Grid.get ig (Index minRow col))) (List.range (Grid.nCols ig)) in
                  Index minRow minColInMinRow),
            -- top-most, break ties by right-most
            ("topRight", flip Ex.map (Ex.zip inputs allNonBlankRows) $ \(ig, nonBlankRows) ->
                let minRow = minimum nonBlankRows
                    maxColInMinRow = maximum $ filter (\col ->
                      nonBlank (Grid.get ig (Index minRow col))) (List.range (Grid.nCols ig)) in
                  Index minRow maxColInMinRow),
            -- bottom-most, break ties by left-most
            ("bottomLeft", flip Ex.map (Ex.zip inputs allNonBlankRows) $ \(ig, nonBlankRows) ->
                let maxRow = maximum nonBlankRows
                    minColInMaxRow = minimum $ filter (\col ->
                      nonBlank (Grid.get ig (Index maxRow col))) (List.range (Grid.nCols ig)) in
                  Index maxRow minColInMaxRow),
            -- bottom-most, break ties by right-most
            ("bottomRight", flip Ex.map (Ex.zip inputs allNonBlankRows) $ \(ig, nonBlankRows) ->
                let maxRow = maximum nonBlankRows
                    maxColInMaxRow = maximum $ filter (\col ->
                      nonBlank (Grid.get ig (Index maxRow col))) (List.range (Grid.nCols ig)) in
                  Index maxRow maxColInMaxRow),
            -- left-most, break ties by top-most
            ("leftTop", flip Ex.map (Ex.zip inputs allNonBlankCols) $ \(ig, nonBlankCols) ->
                let minCol = minimum nonBlankCols
                    minRowInMinCol = minimum $ filter (\row ->
                      nonBlank (Grid.get ig (Index row minCol))) (List.range (Grid.nRows ig)) in
                  Index minRowInMinCol minCol),
            -- left-most, break ties by bottom-most
            ("leftBottom", flip Ex.map (Ex.zip inputs allNonBlankCols) $ \(ig, nonBlankCols) ->
                let minCol = minimum nonBlankCols
                    maxRowInMinCol = maximum $ filter (\row ->
                      nonBlank (Grid.get ig (Index row minCol))) (List.range (Grid.nRows ig)) in
                  Index maxRowInMinCol minCol),
            -- right-most, break ties by top-most
            ("rightTop", flip Ex.map (Ex.zip inputs allNonBlankCols) $ \(ig, nonBlankCols) ->
                let maxCol = maximum nonBlankCols
                    minRowInMaxCol = minimum $ filter (\row ->
                      nonBlank (Grid.get ig (Index row maxCol))) (List.range (Grid.nRows ig)) in
                  Index minRowInMaxCol maxCol),
            -- right-most, break ties by bottom-most
            ("rightBottom", flip Ex.map (Ex.zip inputs allNonBlankCols) $ \(ig, nonBlankCols) ->
                let maxCol = maximum nonBlankCols
                    maxRowInMaxCol = maximum $ filter (\row ->
                      nonBlank (Grid.get ig (Index row maxCol))) (List.range (Grid.nRows ig)) in
                  Index maxRowInMaxCol maxCol)
          ])

    newColors = []
    newShapes = []
    newIdxLists = [] ++
      (if flip Ex.all inputRects (\rs -> flip any rs (\r -> Rect.hasCenter (Shape.enclosingRect r))) then
         [
           -- note how we use non-edge version
           ("rectCenters", flip Ex.map (Ex.zip inputs inputRects) (\(ig, rs) ->
               let rsWithCenter = filter (\r -> Rect.hasCenter (Shape.enclosingRect r)) rs in
                 flip map rsWithCenter (\r -> fromJust (Rect.getCenter (Shape.enclosingRect r)))))
         ]
       else []) ++
      (if flip Ex.all inputSquares (\sqs -> flip any sqs (\sq -> Rect.hasCenter (Shape.enclosingRect sq))) then
         [
           -- note how we use non-edge version
           ("squareCenters", flip Ex.map (Ex.zip inputs inputSquares) (\(ig, sqs) ->
               let sqsWithCenter = filter (\sq -> Rect.hasCenter (Shape.enclosingRect sq)) sqs in
                 flip map sqsWithCenter (\sq -> fromJust (Rect.getCenter (Shape.enclosingRect sq)))))
         ]
       else []) ++
      -- shape enclosing rectangle centers
      (if flip Ex.all orthoColorParse (\shapes -> flip any shapes (\shape -> Rect.hasCenter (Shape.enclosingRect shape))) then
         [
           ("shapeEnclosingRectCenters", flip Ex.map (Ex.zip inputs orthoColorParse) (\(ig, shapes) ->
               let shapesWithCenter = filter (\shape -> Rect.hasCenter (Shape.enclosingRect shape)) shapes in
                 flip map shapesWithCenter (\shape -> fromJust (Rect.getCenter (Shape.enclosingRect shape)))))
         ]
       else [])
    newShapeLists = [] ++
      (if flip Ex.all inputRects (\shapes -> not (null shapes)) then
         [("inputRects", inputRects)]
       else []) ++
      (if flip Ex.all closedShapes (\shapes -> not (null shapes)) then
         [("closedShapes", closedShapes)]
       else []) ++
      (if flip Ex.all oneHoleShapes (\shapes -> not (null shapes)) then
         [("oneHoleShapes", oneHoleShapes)]
       else []) ++
      (if flip Ex.all gt1HoleShapes (\shapes -> not (null shapes)) then
         [("gt1HoleShapes", gt1HoleShapes)]
       else []) ++
      (if flip Ex.all inputSquares (\shapes -> not (null shapes)) then
         [("inputSquares", inputSquares)]
       else []) ++
      (if flip Ex.all orthoColorParse (\shapes -> not (null shapes)) then
         [("orthoColorShapes", orthoColorParse)]
       else []) ++
      (if flip Ex.all biggestShapeLists (\biggestShapes -> isJust biggestShapes) then
         [("biggestShapesList", flip Ex.map biggestShapeLists (\biggestShapes -> fromJust biggestShapes))]
       else []) ++
      (if flip Ex.all smallestShapeLists (\smallestShapes -> isJust smallestShapes) then
         [("smallestShapesList", flip Ex.map smallestShapeLists (\smallestShapes -> fromJust smallestShapes))]
       else [])



shapeFeatureBlast :: StdGoal -> SolveM TacticResult
shapeFeatureBlast tacGoal@(TacGoal.Goal inputs outputs ctx)  = do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  guard $ Ex.all (\ig -> not (Grid.allBlank ig)) inputs
  let reconstructs = initialReconstructs inputs outputs
  let blastCtx     = mergeSynth1Contexts ctx (buildShapeFeatureBlastCtx inputs outputs)
  let safeCtx      = makeBlastCtxSafe blastCtx
  masks            <- Mask.computeMasksFn synthShapeFeatureBlastMasks (tacGoal {TacGoal.synthCtx = safeCtx})
  masks            <- liftIO $ Mask.uniqMasks masks
  candidates       <- Candidate.computeCandidatesFn synthShapeFeatureBlastCandidates (tacGoal {TacGoal.synthCtx = safeCtx})

  -- Right now, we require it to guess
  Blast.blast 6 False masks candidates reconstructs tacGoal True
