-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.ImputeBlanks where

import Data.Maybe (catMaybes)
import Data.Vector.Unboxed.Base (Unbox)
import Util.Imports
import Solver.SolveM
import Solver.Goal
import qualified Data.Map as Map
import Lib.Index (Index(..))
import qualified Lib.Dims as Dims
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import Lib.Symmetry (Symmetry(..))
import qualified Data.Set as Set
import Synth.Ex (Ex(..), ForTrain, ForTest)
import Lib.Grid (Grid)
import qualified Lib.Color as Color
import Lib.Color (Color (..))
import Lib.Dims (Dims(..))
import qualified Util.List as List
import qualified Data.List as List
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Synth1.Basic
import Lib.Blank (isBlank, nonBlank, blank, HasBlank)
import Search.DFS (enumAll)
import Solver.Tactics.Identity (identity)
import qualified Lib.Line as Line
import qualified Lib.Symmetry as Symmetry
import Lib.Axis
import Lib.Direction
import Lib.Rect
import Solver.Tactics.RemoveBlockingColor (removeBlockingColor, getBlockingColors)
import Search.SearchT
import qualified Lib.Tile as Tile
import Lib.Tile

import Debug.Trace

data MajorityImputeOpts = MajorityImputeOpts { majorityThreshold :: Float }

data ImputeBlanksGlobalOpts = ImputeBlanksGlobalOpts { nonBlankThreshold :: Float }

defaultMajorityImputeOpts = MajorityImputeOpts 0.67

defaultImputeBlanksGlobalOpts = ImputeBlanksGlobalOpts 0.23

-- imputeBlanks :: StdGoal -> SolveM TacticResult
-- imputeBlanks goal = do
--   result@(TacticResult.Decompose newGoal@(Goal inputs outputs ctx) _) <- imputeBlanksGlobal goal
--   choice "imputeBlanks"
--     [("identity", 0, identity newGoal),
--      ("imputeBlanksLocal", 0, imputeBlanksLocal newGoal),
--      ("continue", 0, pure result)]

data ImputeTilesOptions = ImputeTilesOptions {
  minShrinkWhenSameSize :: Float
  } deriving (Eq, Ord, Show)

defaultImputeTilesOptions = ImputeTilesOptions { minShrinkWhenSameSize = 0.5 }

imputeBlanksByTiling goal@(Goal inputs outputs ctx) = do
  (trainBlockingColors, trainKeepColors) <- getBlockingColors goal -- guards for samedims, only reports non-blank non-keep colors
  -- there is a single (possibly blank) blocking color in all test inputs

  -- liftIO . traceIO $ show trainBlockingColors

  guard $ (all ((==1).Set.size) trainBlockingColors) && ((==1) . Set.size $ Set.unions trainBlockingColors)

  blockingColor <- oneOf "blockingColor" [((\x -> (show x, x)) . Set.elemAt 0 . head $ trainBlockingColors)]

  guard $ flip all trainKeepColors $ \keepColors ->
    not . Set.null $ (Set.difference (Set.difference keepColors $ Set.singleton blockingColor) (Set.singleton blank))
    
  -- liftIO . traceIO $ "BLOCKING COLOR: " ++ show blockingColor

  -- liftIO . traceIO $ "KEEP COLORS: " ++ show trainKeepColors

  guard $ isBlank blockingColor <= (flip all trainKeepColors $ \keepColors -> not $ blank `elem` keepColors)

  let eqModuloBlockingColor c1 c2 = (c1 == c2) || (c1 == blockingColor) || (c2 == blockingColor)

  -- liftIO . traceIO $ "TEST EQ MODULO BLOCKING COLOR: " ++ show (eqModuloBlockingColor blockingColor 2, eqModuloBlockingColor blockingColor blockingColor, eqModuloBlockingColor 3 4)

  -- for each training example, try synthesizing a strict tiling which tiles the input modulo the blocking color
  flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) -> do
    deltas <- oneOf "deltas" [("[0]", [0]), ("[-1,1]", [-1, 1])]
    tData@(Tile.TileData tDataDims tDataDelta) <- liftO $ Tile.findMinimalTilePred deltas (==) output
    guard $ Tile.isTiling eqModuloBlockingColor input tData
    guard $ (Grid.sameDims input output) <= (fromIntegral (Dims.nCells tDataDims) <= fromIntegral (Dims.nCells (Grid.dims input)) * minShrinkWhenSameSize defaultImputeTilesOptions)
    -- liftIO . traceIO $ "SYNTHESIZED TILING: " ++ show tData



  -- synthesize a tiling on the test inputs which tiles the inputs modulo the blocking color, and use that to make the guess

  let reduceModuloBlockingColor c1 c2 =
        if c1 == blockingColor then c2 else
          if c2 == blockingColor then c1 else c1

  testTileDicts :: ForTest (TileData, Map Index Color) <- flip mapM (Ex.test inputs) $ \input -> do
    deltas <- oneOf "deltas" [("[0]", [0]), ("[-1,1]", [-1, 1])]
    liftO $ findMinimalTilePredDict deltas eqModuloBlockingColor input reduceModuloBlockingColor

  -- liftIO . traceIO $ "TESTTILEDICTS: " ++ show testTileDicts
  
    -- TODO: special support when blocking color is not among the keeps; then we can guard that the
    -- joined tile does not contain the blocking color whatsoever
    -- in general, the blocking color might be part of the output, e.g. ea959feb

  guesses <- flip mapM (zip (Ex.test inputs) testTileDicts) $ \(input, (tData, tileDict)) -> do
    flip Grid.mapM input $ \idx c -> liftO $ do
      v <- flip Map.lookup tileDict $ Tile.applyIndex tData idx
      guard $ (c /= v) <= (c == blockingColor)
      pure v

  guard $ (flip all (outputs) (Grid.containsVal blank)) <= (flip all guesses $ Grid.containsVal blank)
  guard $ (flip all (outputs) (not . (Grid.containsVal blank))) <= (flip all guesses $ not . (Grid.containsVal blank))
  guard $ (flip any guesses $ Grid.containsVal blank) <= (flip any (outputs) (Grid.containsVal blank)) -- not sure about this one

  pure $ TacticResult.Guess guesses


imputeBlanksGlobal goal@(Goal inputs outputs ctx) (ImputeBlanksGlobalOpts thresh) = do
  -- guard $ flip Ex.any inputs $ \input -> Grid.containsVal blank input
  guard $ let fracs = flip map (Ex.toBigList inputs) $ Grid.nonBlankFrac in
          all (thresh <) fracs && any (< 1.0) fracs
  choice "imputeBlanksGlobal"
    [
      ("imputeBlanksBySymmetry", imputeBlanksBySymmetry goal)
    ]

imputeBlanksBySymmetry goal@(Goal inputs outputs ctx) = do
  symss :: Ex [Symmetry] <- do
    trainSymmetries :: [Symmetry] <- do
      allSymmetries <- enumAll $ Symmetry.enumProperSymmetries
      pure $ flip filter allSymmetries $ \sym ->
        flip all outputs $ \output -> -- trace (show (sym, Symmetry.eqUptoSymmetry output sym output)) $
          Symmetry.eqUptoSymmetry output sym output

    guard . not . null $ trainSymmetries
    pure $ Ex.replicate (Ex.getInfo inputs) trainSymmetries

  newInputs :: Ex (Grid Color) <- flip Ex.mapM (Ex.zip inputs symss) $ \(input, syms) -> do
    result <- liftO $ gridImputeBlanksBySymmetries input syms
    guard $ Dims.any (Grid.dims result) $ \idx -> Grid.get input idx /= Grid.get result idx
    pure result

  choice "imputeBlanksBySymmetry"
    [
      ("crop", (do
         let commonSyms = foldr1 List.intersect (Ex.toBigList symss)
         let nGlobalSyms = length commonSyms
         let reflectAxes = flip map (filter Symmetry.isReflect $ commonSyms) $ \sym -> -- maybe don't guard on this? idk
               case sym of
                 SymReflect axis -> axis

         -- for now, ensure that we get more symmetries
         let reflectAxesCounts = List.iter reflectAxes (Map.fromList (zip [Horizontal, Vertical, DownRight, DownLeft] [0,0,0,0])) $ \acc ax ->
               pure $ Map.insertWith (+) ax 1 acc

         guard . not . null $ reflectAxes

         allSymmetries <- enumAll $ Symmetry.enumProperSymmetries
         let axDirs = do
               ax <- [Horizontal, Vertical, DownRight, DownLeft]
               dir <- [Normal, Reverse]
               pure (ax, dir)

         let computeGridSymmetries grid = flip filter allSymmetries $ \sym -> Symmetry.eqUptoSymmetry grid sym grid

         outSymSubgrids <- choice "outSymSubgrids"
           [
             ("first", do
                 let computeSymRect grid ax dir = -- TODO(jesse): just compute them all? we have plenty of time
                       flip List.first (drop 1 $ Grid.cropDeltas grid ax) $ \delta -> do
                         subGrid <- Grid.getRect grid <$> Grid.cropAlongAxDirOpt grid ax dir delta
                         let subGridSyms = computeGridSymmetries subGrid
                         guard $ (not $ null subGridSyms) && length subGridSyms > ((Map.!) reflectAxesCounts ax)
                         pure ((ax, dir, delta), subGridSyms)
                 let outSymSubgrids = flip map outputs $ \output ->
                       catMaybes $ flip map axDirs $ \(ax, dir) -> computeSymRect output ax dir
                 pure outSymSubgrids
             ),

             ("more", do
                let computeSymRectAll :: Grid Color -> Axis -> Direction -> [Maybe ((Axis, Direction, Int), [Symmetry])]
                    computeSymRectAll grid ax dir = do -- yolo
                      delta <- (drop 1 $ Grid.cropDeltas grid ax)
                      pure $ do
                        subGrid <- Grid.getRect grid <$> Grid.cropAlongAxDirOpt grid ax dir delta
                        let subGridSyms = computeGridSymmetries subGrid
                        guard $ (not $null subGridSyms) && length subGridSyms > ((Map.!) reflectAxesCounts ax)
                        pure ((ax, dir, delta), subGridSyms)

                let outSymSubgridsAll = flip map outputs $ \output ->
                      catMaybes . List.concat $ flip map axDirs $ \(ax, dir) ->
                        computeSymRectAll output ax dir

                pure outSymSubgridsAll
                 )
           ]

         sharedCrops <- oneOf "crop" $ [(\x -> ("SHARED CROPS: " ++show x, x)) $ foldr1 List.intersect (outSymSubgrids)]

         guard . not . null $ sharedCrops

         let guessCrops = Ex.replicate (Ex.getInfo newInputs) sharedCrops

         let imputeCrop :: Grid Color -> ((Axis, Direction, Int), [Symmetry]) -> SolveM (Grid Color)
             imputeCrop grid ((ax,dir,delta), syms) = do
               (Rect index dims) <- liftO $ Grid.cropAlongAxDirOpt grid ax dir delta
               Grid.replaceSubgridUnsafeM grid dims index $ liftO . (flip gridImputeBlanksBySymmetries syms)

         let imputeCrops grid crops = List.iterM crops grid imputeCrop

         newInputs <- flip Ex.mapM (Ex.zip newInputs guessCrops) $ uncurry imputeCrops

         guard $ flip all (zip (Ex.train newInputs) outputs) $ uncurry Grid.subset

         (pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure) >>= pop 1 . pure)
      ),
      ("continue", pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure)
    ]

gridImputeBlanksBySymmetries :: (Unbox a, HasBlank a, Show a) => Grid a -> [Symmetry] -> Maybe (Grid a)
gridImputeBlanksBySymmetries input syms = List.iterM syms input $ \acc sym -> gridImputeBlanksBySymmetry acc sym

gridImputeBlanksBySymmetry :: (Unbox a, HasBlank a, Show a) => Grid a -> Symmetry -> Maybe (Grid a)
gridImputeBlanksBySymmetry input sym = do
  let gridZip g1 g2 = do
        guard $ Grid.sameDims g1 g2
        pure $ flip Grid.map g1 $ \idx c -> (c, Grid.get g2 idx)
  inputAux <- (Symmetry.apply sym input >>= gridZip input)
  flip Grid.mapM inputAux $ \_ (c1, c2) -> do
    guard (c1 == blank || c2 == blank || c1 == c2)
    flip List.find [c1,c2] (/= blank) <|> pure blank

-- precondition: outputs contain no blanks, inputs contain some blanks, samedim inputs and outputs
-- postcondition: guesses contains no blanks
imputeBlanksLocal goal@(Goal inputs outputs ctx) = do
  guardIsImputeProblem goal
  guard $ flip all outputs $ \output -> not $ Grid.containsVal blank output
  choice "imputeBlanksLocal" [("imputeBlanksByMajority", imputeBlanksByMajority goal)]

imputeBlanksByMajority goal@(Goal inputs outputs ctx) = do
  candidatesFn <- choice "byMajorityCandidatesFn"
    [("axes", do
         ax :: Axis <- enumVals
         pure $ \input idx -> (Line.idxsOnLine (Grid.dims input) $ Line.lineWith (Grid.dims input) idx ax)),
      ("neighbors", pure $ \input idx -> Grid.neighbors input idx)]

  let majorityGuess input idx opts = do
        let candidates = map (Grid.get input) $ candidatesFn input idx
        domElem <- Grid.getDominantElem candidates (majorityThreshold opts)
        guard $ nonBlank domElem
        pure domElem

  guard $ flip all (zip (Ex.train inputs) outputs) $ \(input, output) ->
    Dims.all (Grid.dims input) $ \idx -> isJust $ do
      let c = Grid.get input idx
      if isBlank c then do
        cGuess <- majorityGuess input idx defaultMajorityImputeOpts
        guard (cGuess == Grid.get output idx)
        pure ()
        else pure ()

  guesses <- flip mapM (Ex.test inputs) $ \input ->
    flip Grid.mapM input $ \idx c ->
      if nonBlank c
        then pure c
        else liftO $ majorityGuess input idx defaultMajorityImputeOpts

  pure $ TacticResult.Guess guesses

guardIsImputeProblem :: StdGoal -> SolveM ()
guardIsImputeProblem goal@(Goal inputs outputs ctx) = do
  let trainExamples = zip (Ex.train inputs) outputs
  guard $ all (uncurry Grid.sameDims) trainExamples
  guard $ flip any (Ex.train inputs) $ \input -> Grid.containsVal blank input
  guard $ flip all (Ex.test inputs) $ \input -> Grid.containsVal blank input
  guard $ flip all trainExamples $ \(input, output) ->
    Dims.all (Grid.dims input) $ \idx ->
      let cIn = Grid.get input idx; cOut = Grid.get output idx in
        (cIn /= cOut) <= isBlank cIn
