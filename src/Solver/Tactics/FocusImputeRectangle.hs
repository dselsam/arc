-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.FocusImputeRectangle where

import Data.Vector.Unboxed.Base (Unbox)
import Util.Imports
import Solver.SolveM
import Search.SearchT
import Solver.Goal
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import Lib.Symmetry (applyIndex, Symmetry(..))
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import Lib.Color (Color)
import Lib.Dims (Dims(..))
import qualified Util.List as List
import qualified Data.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Solver.Synth1Context (Synth1Context(..))
import Synth1.Basic
import Lib.Blank (isBlank, blank, nonBlank)
import Solver.Tactics.ImputeBlanks (imputeBlanksBySymmetry, gridImputeBlanksBySymmetry, gridImputeBlanksBySymmetries)
import Solver.Tactics.RemoveBlockingColor (removeBlockingColor)
import Solver.Tactics.GuessDims (synthDims)
import Search.DFS
import Debug.Trace
import Synth.Core
import Synth.Basic
import Synth.Spec.ESpec
import Solver.Tactics.DyeInputs (synthG2C)
import qualified Lib.Parse as Parse
import qualified Lib.Shape as Shape
import qualified Lib.Rect as Rect
import Lib.Rect (Rect)
import Lib.Shape (Shape)
import Lib.Axis
import Lib.Direction
import Lib.Rect
import Data.Maybe (catMaybes)

focusImputeRectangle :: StdGoal -> SolveM TacticResult
focusImputeRectangle goal@(Goal inputs outputs ctx) = do
  guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
    Grid.dims output < Grid.dims input

  -- find monochromatic rectangles of color C of same dims as output such that C is not in output
  (trainCandidateIndices :: ForTrain (Index, Dims, Color)) <- List.iterM (zip (Ex.train inputs) outputs) [] $ \acc (input, output) -> do
    let outDims = (Grid.dims output)
    let rectIndices = Grid.findSubgrids input outDims  $ \subgrid ->
          case Grid.isUniform subgrid of
            Nothing -> False
            (Just cIn) -> not $ Grid.containsVal cIn output
    guard $ length rectIndices == 1
    let rectIndex = head rectIndices
    let cRect = Grid.get input $ rectIndex
    pure $ (++) acc . pure $ (rectIndex, outDims, cRect)

  (testCandidateIndices :: ForTest (Index, Dims, Color)) <- choice "focusImputeRectangle"
    [
      ("fromDims", do
          testDims <- synthDims goal
          List.iterM (zip (Ex.test inputs) testDims) [] $ \acc (input, outDims) -> do
            let rectIndices = Grid.findSubgrids input outDims  $ \subgrid ->
                  case Grid.isUniform subgrid of
                    Nothing -> False
                    (Just cIn) -> True
            guard $ length rectIndices == 1
            let rectIndex = head rectIndices
            let cRect = Grid.get input $ rectIndex
            pure $ (++) acc . pure $ (rectIndex, outDims, cRect)       
      ),

      ("fromColor", do
          testColors <- runSynth11 ctx $ synthG2C inputs $ (\(_,_,x) -> x) <$> trainCandidateIndices
          (parser :: Grid Color -> [Shape Color]) <- choice "parse" -- sorry if this isn't idiomatic
            [
              ("localOrthoNoBlanksByColor", pure $ flip Parse.parseScene $ Parse.Options Parse.ParseLocalOrtho Parse.ParseNoBlanksByColor),
               ("localOrthoOnlyBlanks", pure $ flip Parse.parseScene $ Parse.Options Parse.ParseLocalOrtho Parse.ParseOnlyBlanks)
            ]
      
          testRects <- flip mapM (zip testColors $ (parser <$> (Ex.test inputs))) $
            \(color, shapes) -> Shape.enclosingRect <$> choice "pickRect"
              [
                ("largest", do
                    let candidateRects = flip filter shapes $ \shape ->
                          Shape.isFilledRect shape && (isJust $ Shape.uniformColorOpt shape >>= guard . (==color))
                    guard . not . null $ candidateRects
                    pure $ flip List.maximumBy candidateRects $ comparing Shape.nPoints
                )
              ]
              
          pure $ flip map (zip testRects testColors) $ \((Rect.Rect ul dims), color) -> (ul, dims, color)
      )
    ]

  -- liftIO . traceIO $ "WHAT"
  -- liftIO . traceIO $ show testCandidateIndices

  (TacticResult.Decompose (Goal symInputs _ _) _) <- find1 "focusImputeRectangle" $ do
    let candidateIndices = Ex trainCandidateIndices testCandidateIndices

    -- blank out the train rectangles and symmetrify
    let tmpInputs = flip Ex.map (Ex.zip inputs $ candidateIndices) $ \(input, ((rectIdx,dims,c0))) ->
          flip Grid.map input $ \idx c ->
            if c == c0 && (Dims.inBounds dims (idx - rectIdx)) then blank else c
    let trainRectIndices = (\(x,_,_) -> x) <$> trainCandidateIndices
    let trainRectDims = (\(_,x,_) -> x) <$> trainCandidateIndices
    imputeBlanksBySymmetryModSubgrid (Goal tmpInputs outputs ctx) trainRectIndices trainRectDims

  -- liftIO . traceIO $ "WHAT?"

  -- liftIO . traceIO $ show symInputs
  
  -- maybe cleaner to focus *> identity
  guard $ flip all (zip (Ex.train symInputs) (zip trainCandidateIndices outputs)) $ \(input, ((index, dims, c), output)) ->
    Grid.getSubgridUnsafe input dims index == output

  -- liftIO . traceIO $ "WHAT??"
  
  (guesses :: ForTest (Grid Color)) <- flip mapM (zip (Ex.test symInputs) testCandidateIndices) $ \(input, (index, dims, c)) -> do
        let guess = Grid.getSubgridUnsafe input dims index
        guard $ Grid.containsVal blank guess <=
          (Dims.any (Grid.dims input) $ \idx ->
              (not $ Rect.containsIndex (Rect index dims) idx) && (isBlank $ Grid.get input idx))
        pure guess

  pure $ TacticResult.Guess guesses

eqUptoSymmetryModSubgrid :: (Unbox a, Eq a, Show a) => Grid a -> Symmetry -> Grid a -> Index -> Dims -> Bool
eqUptoSymmetryModSubgrid g1 sym g2 rectIdx rectDims =
  let result = do
        guard $ Grid.dims g1 == Grid.dims g2
        encode2 <- applyIndex (Grid.dims g1) sym
        -- pure $ Dims.all (Grid.dims g1) $ \idx ->
        --   let okIdx idx = not $ ((Dims.inBounds rectDims $ idx - rectIdx) || (Dims.inBounds rectDims $ (encode2 idx)-rectIdx)) in
        --   if okIdx idx then Grid.get g1 idx == Grid.get g2 (encode2 idx) else True
        Dims.iterM (Grid.dims g1) True $ \acc idx -> do
          guard acc
          let okIdx idx = not $ ((Dims.inBounds rectDims $ idx - rectIdx) || (Dims.inBounds rectDims $ (encode2 idx)-rectIdx))
          let flag = Grid.get g1 idx == Grid.get g2 (encode2 idx)
          if okIdx idx then pure (acc && Grid.get g1 idx == Grid.get g2 (encode2 idx)) else pure True
  in
    case result of
      Nothing -> False
      Just b -> b

imputeBlanksBySymmetryModSubgrid :: StdGoal -> ForTrain Index -> ForTrain Dims -> SolveM TacticResult
imputeBlanksBySymmetryModSubgrid goal@(Goal inputs outputs ctx) rectIdxs rectDimss = do
  symss :: Ex [Symmetry] <- do
    trainSymmetries :: [Symmetry] <- do
      allSymmetries <- enumAll $ Symmetry.enumProperSymmetries
      pure $ flip filter allSymmetries $ \sym ->
        flip all (zip (Ex.train inputs) (zip rectIdxs rectDimss)) $ \(input, (rectIdx, rectDims)) -> eqUptoSymmetryModSubgrid input sym input rectIdx rectDims
    -- guard . not . null $ trainSymmetries
    pure $ Ex.replicate (Ex.getInfo inputs) trainSymmetries

  -- liftIO . traceIO $ "SYMSS: " ++ show symss

  newInputs :: Ex (Grid Color) <- flip Ex.mapM (Ex.zip inputs symss) $ \(input, syms) -> do
    List.iterM syms input $ \acc sym -> liftO $ gridImputeBlanksBySymmetry acc sym

  let continueFlag = -- have we already satisfied the spec?
        flip all (zip3 (Ex.train newInputs) (zip rectIdxs rectDimss) outputs) $ \(input, (idx, dims), output) ->
          Grid.getSubgridUnsafe input dims idx == output

  choice "imputeBlanksBySymmetryModSubgrid"
    [
      ("cropModSubgrid", (do
         guard $ not continueFlag
         guard $ flip Ex.any newInputs $ Grid.containsVal blank
         let commonSyms = foldr1 List.intersect (Ex.toBigList symss)
         let nGlobalSyms = length commonSyms
         let reflectAxes = flip map (filter Symmetry.isReflect $ commonSyms) $ \sym -> -- maybe don't guard on this? idk
               case sym of
                 SymReflect axis -> axis

         -- for now, ensure that we get more symmetries
         let reflectAxesCounts = List.iter reflectAxes (Map.fromList (zip [Horizontal, Vertical, DownRight, DownLeft] [0,0,0,0])) $ \acc ax ->
               pure $ Map.insertWith (+) ax 1 acc
         -- guard . not . null $ reflectAxes -- meh

         allSymmetries <- enumAll $ Symmetry.enumProperSymmetries
         let computeGridSymmetriesModSubgrid grid idx dims = flip filter allSymmetries $ \sym ->
               eqUptoSymmetryModSubgrid grid sym grid idx dims

         let computeSymRectModSubgrid grid ax dir idx dims = -- TODO(jesse): just compute them all? we have plenty of time
               flip List.first (Grid.cropDeltas grid ax) $ \delta -> do
                 rect@(Rect idx0 _) <- Grid.cropAlongAxDirOpt grid ax dir delta
                 let rectIntersect = Rect.intersect rect (Rect idx dims)
                 let subIdx@(Index iSub jSub) = Rect.upperLeft rectIntersect - idx0
                 let subDims@(Dims subNRows subNCols) = Rect.dims rectIntersect
                 let subGrid = Grid.getRect grid rect
                 guard $ iSub >= 0 && jSub >= 0 && subNRows > 0 && subNCols > 0
                 -- trace (show (subIdx, subDims)) $ pure ()
                 -- trace ("OK") $ pure ()
                 let subGridSyms = computeGridSymmetriesModSubgrid subGrid subIdx subDims
                 -- trace ("OK!") $ pure ()
                 guard $ length subGridSyms > ((Map.!) reflectAxesCounts ax)
                 -- trace ("OK!!") $ pure ()
                 pure ((ax, dir, delta), subGridSyms)

         let axDirs = do
               ax <- [Horizontal, Vertical, DownRight, DownLeft]
               dir <- [Normal, Reverse]
               pure (ax, dir)

         let trainSymSubgrids = flip map (zip (Ex.train newInputs) (zip rectIdxs rectDimss)) $ \(input, (idx, dims)) ->
               catMaybes $ filter isJust $ flip map axDirs $ \(ax, dir) -> computeSymRectModSubgrid input ax dir idx dims

         -- trace ("DETECTED SYMMETRIES: ") $ List.iterM trainSymSubgrids () $ \_ x -> liftIO . traceIO . show $ x

         sharedCrops <- oneOf "crop" $ [(\x -> ("SHARED CROPS: " ++show x, x)) $ foldr1 List.intersect (trainSymSubgrids)]

         guard . not . null $ sharedCrops

         let guessCrops = Ex.replicate (Ex.getInfo newInputs) sharedCrops

         let imputeCrop :: Grid Color -> ((Axis, Direction, Int), [Symmetry]) -> SolveM (Grid Color)
             imputeCrop grid ((ax,dir,delta), syms) = do
               (Rect index dims) <- liftO $ Grid.cropAlongAxDirOpt grid ax dir delta
               Grid.replaceSubgridUnsafeM grid dims index $ liftO . (flip gridImputeBlanksBySymmetries syms)

         let imputeCrops grid crops = List.iterM crops grid imputeCrop

         newInputs <- flip Ex.mapM (Ex.zip newInputs guessCrops) $ uncurry imputeCrops

         (pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure) >>= pop 1 . pure)
      ),
      ("continue", pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure)
    ]

