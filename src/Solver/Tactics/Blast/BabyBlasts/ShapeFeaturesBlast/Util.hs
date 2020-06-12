{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Blast.BabyBlasts.ShapeFeaturesBlast.Util where

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
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Lib.HasElems


-- assuming the check has already been done
-- wil lhav esome fold that checks if all just, if so passes this with the isJusts, else ctx
-- handles SINGLE shapes (e.g., the BIGGEST rect). Doesn't handle
addShapeFeatures :: Ex (Grid Color) -> String -> Ex (Shape Color) -> Synth1Context -> Synth1Context
addShapeFeatures inputs shapeSetName shapes ctx =
  ctx {
       ctxInts = (ctxInts ctx) ++ newInts,
       ctxColors = (ctxColors ctx) ++ newColors,
       ctxIdxs = (ctxIdxs ctx) ++ newIdxs,
       ctxIdxLists = (ctxIdxLists ctx) ++ newIdxLists,
       ctxShapes = (ctxShapes ctx) ++ newShapes
      }
  where

    enclosingRects = flip Ex.map shapes $ \s -> Shape.enclosingRect s

    newInts = []

    newColors = [(shapeSetName ++ "Color", flip Ex.map shapes $ \s -> List.mostCommon $ Shape.valuesToList s)]

    newIdxs = [] ++
      (if flip Ex.all enclosingRects (\r -> Rect.hasCenter r) then
        [(shapeSetName ++ "EnclosingRectCenter", flip Ex.map enclosingRects (\r ->
            fromJust (Rect.getCenter r)))]
      else []) ++
      -- for each corner, add if none of them are on the edge
      (List.iter elems [] (\acc corn ->
        if flip Ex.all (Ex.zip enclosingRects inputs) (\(r, ig) -> not (Dims.onEdge (Grid.dims ig) (Rect.getCorner r corn)))
        then pure $ acc ++
          [(shapeSetName ++ "EnclosingRect" ++ (show corn), flip Ex.map enclosingRects (\r -> Rect.getCorner r corn))]
        else pure acc))


    newIdxLists = [
      (shapeSetName ++ "EnclosingRectNonEdgeCorners", flip Ex.map (Ex.zip inputs enclosingRects) (\(ig, r) ->
          Rect.getNonEdgeCorners (Grid.dims ig) r))
      , (shapeSetName ++ "EnclosingRectPerimeterIdxs", flip Ex.map enclosingRects (\r ->
          Rect.getPerimeterIdxs r))
      , (shapeSetName ++ "EnclosingRectInteriorIdxs", flip Ex.map enclosingRects (\r ->
          Rect.getInteriorIdxs r))
      ]

    newShapes = [(shapeSetName, flip Ex.map shapes id)]
