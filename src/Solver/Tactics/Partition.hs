-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Solver.Tactics.Partition where

import Debug.Trace
import Data.List (zip4)
import Data.Ratio
import Util.Imports
import Lib.Blank
import Util.List (range, first, countDistinct, allSame)
import qualified Util.Int as Int
import qualified Lib.Color as Color
import Lib.Color (Color(Color))
import qualified Data.Maybe as Maybe
import Solver.SolveM
import Solver.Goal
import Solver.Synth1Context
import Lib.Index
import Synth1.Basic
import qualified Lib.Dims as Dims
import qualified Lib.Rect as Rect
import Lib.Rect (Rect(Rect))
import qualified Lib.BGrid as Box
import Search.DFS
import Lib.Dims (Dims(..))
import qualified Data.Set as Set
import Lib.Color (Color)
import Lib.Grid (Grid, PartitionSepData(..))
import Synth.Ex (Ex, ForTrain, ForTest)
import qualified Util.List as List
import qualified Synth.Ex as Ex
import qualified Lib.Grid as Grid
import Solver.TacticResult (TacticResult)
import qualified Solver.TacticResult as TacticResult
import Search.SearchT
import Solver.Tactics.Identity
import Solver.Tactics.TrySolveGG2GG
import Solver.Tactics.TrySolveGG2G
import Solver.Tactics.ColorMap
import Solver.Tactics.InputSymmetries
import Solver.Tactics.Blast.BabyBlasts.ColorBlast.ColorBlast (colorBlast)

---------------
-- Partition
---------------
-- Requires:
--   - TODO
-- Considers:
--   - TODO
-- TODO:
--   - uniform with ones at beginning and/or end?
--   - partition upto mask?
--   - all lines but only uniform colors?

data PartitionSepKind = SepEven | SepUniformLines deriving (Eq, Ord, Show)

data PartitionSepReconstructData = PartitionSepReconstructData {
  pDatas       :: ForTest PartitionSepData,
    baseGrids    :: ForTest (Grid Color)
  } deriving (Eq, Ord, Show)

-- Just high enough for 0b148d64
-- (but hopefully too low for a jillion other annoying fires)
maxDensityInRest :: Float
maxDensityInRest = 0.3

partition :: StdGoal -> SolveM TacticResult
partition goal =
  choice "partition" [
  ("sep",    partitionSep goal)
  , ("even", partitionEven goal)
    ]

enumPartitionSepFn :: SolveM (PartitionSepKind, Grid Color -> Maybe (PartitionSepData, Color))
enumPartitionSepFn =
  oneOf "enumPartitionSepFn" [
  ("uniform",           partitionUniform)
  , ("allLinesUniform", partitionAllLinesUniform)
  ]
    where
      partitionUniform = (SepEven, \g -> do
        guard $ not . isJust $ Grid.isUniform g
        let onSame i i2 = mod (i2+1) (i+1) == 0
        let hLines = listFromOpt $ Int.first (1 + div (Grid.nRows g) 2) $ \i -> do
              guard $ i > 0 && i < Grid.nRows g
              x <- Grid.rowIsUniform g i
              guard $ Int.all (Grid.nRows g) $ \i2 ->
                if onSame i i2 then Grid.rowIsUniform g i2 == Just x else Grid.rowIsUniform g i2 /= Just x
              pure  $ filter (onSame i) (range (Grid.nRows g))
        let vLines = listFromOpt $ Int.first (1 + div (Grid.nCols g) 2) $ \j -> do
              guard $ j > 0 && j < Grid.nCols g
              x <- Grid.colIsUniform g j
              guard $ Int.all (Grid.nCols g) $ \j2 ->
                if onSame j j2 then Grid.colIsUniform g j2 == Just x else Grid.colIsUniform g j2 /= Just x
              pure  $ filter (onSame j) (range (Grid.nCols g))
        guard (not (null hLines && null vLines))
        guard $ (Grid.nRows g == 1) <= (length vLines > 1)
        guard $ (Grid.nCols g == 1) <= (length hLines > 1)
        let x = if null hLines then Grid.get g (Index 0 $ head vLines) else Grid.get g (Index (head hLines) 0)
        -- The point is that you can partition even (in 1-D) even when there are lines of *other* colors
        -- (whereas you can't partitionAllLines unless it is the only color with a line)
        guard $ hLines == Grid.horizontalLinesColor x g
        guard $ vLines == Grid.verticalLinesColor x g

        guard $ acceptableDensity g x hLines vLines
        pure (PartitionSepData hLines vLines, x))

      partitionAllLinesUniform = (SepUniformLines, \g -> do
        -- TODO: could be 1d with multiple, how to handle backtracking?
        --  for now we just take the first
        let colors = collectLineColors g
        guard $ not (null colors)
        guard $ length colors == 1 -- TODO: reconsider
        let x = head colors
        let hLines = Grid.horizontalLinesColor x g
        let vLines = Grid.verticalLinesColor x g
        guard $ length hLines < Grid.nRows g
        guard $ length vLines < Grid.nCols g
        guard $ not (null hLines && null vLines)
        let hRuns = computeRuns hLines
        let vRuns = computeRuns vLines
        guard $ runsOk x (Grid.nRows g) hLines hRuns
        guard $ runsOk x (Grid.nCols g) vLines vRuns
        guard $ acceptableDensity g x hLines vLines
        pure (PartitionSepData hLines vLines, x))

      runsOk :: Color -> Int -> [Int] -> [Int] -> Bool
      runsOk x k []     []    = True
      runsOk x k lines0 runs0 = someLineInMiddle k lines0 runs0
        && (if isBlank x then uniform runs0 else uniformExceptForEdges k lines0 runs0)

        where
          someLineInMiddle k lines0 runs0 =
            let nTouchingEdge = length $ filter id [0 `elem` lines0, (k-1) `elem` lines0] in
              length runs0 > nTouchingEdge

          uniform runs0 = List.countDistinct id runs0 == 1

          uniformExceptForEdges k lines0 runs0 =
            let (lines1, runs1) =
                  if 0 `elem` lines0 && head runs0 < head (tail runs0)
                  then (drop (head runs0) lines0, tail runs0)
                  else (lines0, runs0)
                (lines2, runs2) =
                  if (k-1) `elem` lines1 && last runs1 < head runs1
                  then (take (length lines1 - last runs1) lines1, init runs1)
                  else (lines1, runs1)
            in
              List.countDistinct id runs2 == 1

      acceptableDensity :: Grid Color -> Color -> [Int] -> [Int] -> Bool
      acceptableDensity g x hLines vLines =
        -- TODO: extra strict for blank?
        let hs :: Set Int = Set.fromList hLines
            vs :: Set Int = Set.fromList vLines
            (nOutside, nTotal) = Dims.iter (Grid.dims g) (0, 0) $ \(nOutside, nTotal) idx@(Index i j) -> pure $
              if not (i `elem` hs || j `elem` vs) && Grid.get g idx == x
              then (nOutside + 1, nTotal + 1)
              else (nOutside, nTotal + 1)
        in
          (fromIntegral nOutside) / (fromIntegral nTotal) < maxDensityInRest

      computeRuns :: [Int] -> [Int]
      computeRuns [] = []
      computeRuns (x:xs) = computeRunsCore xs x 1 []

      computeRunsCore :: [Int] -> Int -> Int -> [Int] -> [Int]
      computeRunsCore []     prevVal prevRun acc = prevRun:acc
      computeRunsCore (x:xs) prevVal prevRun acc =
        if x == prevVal + 1
        then computeRunsCore xs x (prevRun + 1) acc
        else computeRunsCore xs x 1 (prevRun:acc)

      collectLineColors g =
        let rowColors = Int.iter (Grid.nRows g) Set.empty $ \acc i ->
              case Grid.rowIsUniform g i of
                Nothing -> acc
                Just x -> Set.insert x acc
        in
          Set.toList $ Int.iter (Grid.nCols g) rowColors $ \acc j ->
            case Grid.colIsUniform g j of
              Nothing -> acc
              Just x -> Set.insert x acc

      listFromOpt (Just xs) = xs
      listFromOpt Nothing   = []

partitionSep :: StdGoal -> SolveM TacticResult
partitionSep goal@(Goal inputs outputs ctx) = do
  (pSepKind, partitionSepFn, pInputsData, pInputsColors, pInputs) <- do
    (pSepKind, partitionSepFn) <- enumPartitionSepFn
    -- TODO: support partitionSepFn that only works on outputs
    pInputsSepResults <- liftO $ Ex.mapM partitionSepFn inputs
    let pInputsData = Ex.map fst pInputsSepResults
    let pInputsColors = Ex.map snd pInputsSepResults
    pInputs <- liftO $ Ex.mapM (uncurry Grid.partitionSepWith) (Ex.zip inputs pInputsData)
    pure (pSepKind, partitionSepFn, pInputsData, pInputsColors, pInputs)

  let newCtx = if countDistinct id (Ex.train pInputsColors ++ Ex.test pInputsColors) > 1
               then ctx { ctxColors = ("partitionSep", pInputsColors):ctxColors ctx }
               else ctx

  choice "partitionSep" [
    ("partitionSepIO",   partitionSepIO pSepKind partitionSepFn pInputsData pInputsColors pInputs newCtx)
    , ("partitionSepI",  partitionSepI pSepKind pInputsColors pInputs newCtx)
    ]

  where
    partitionSepIO pSepKind partitionSepFn pInputsData pInputsColors pInputs newCtx = do
      pOutputsData <- map fst <$> (liftO $ mapM partitionSepFn outputs)
      pOutputs <- liftO $ mapM (uncurry Grid.partitionSepWith) (zip outputs pOutputsData)
      -- TODO: worth the check?

      -- 2 cases:
      --   - 1. all the outputs have the same partition (& colors) as each other
      --   - 2. all the outputs have the same partition (& colors) as the input
      reconstructData :: PartitionSepReconstructData <- liftO $ do
        let output0 = head outputs
        let pData0  = head pOutputsData
        if all (\(output, pData) -> pData == pData0 && Grid.sameUnpartitionSep pData0 output0 output) (zip outputs pOutputsData)
          then pure $ PartitionSepReconstructData { pDatas = map (\_ -> pData0) (Ex.test inputs), baseGrids = map (\_ -> output0) (Ex.test inputs) }
             else if all (\(input, output, pDataIn, pDataOut) -> pDataIn == pDataOut && Grid.sameUnpartitionSep pDataIn input output)
                  (zip4 (Ex.train inputs) outputs (Ex.train pInputsData) pOutputsData)
               then pure $ PartitionSepReconstructData { pDatas = Ex.test pInputsData, baseGrids = Ex.test inputs }
               else Nothing

      let reconstructGG2G :: ForTrain (Box.Grid (Grid Color)) -> Maybe (ForTrain (Grid Color))
          reconstructGG2G guesses = do
            flip mapM (zip3 (pDatas reconstructData) (baseGrids reconstructData) guesses) $ \(pData, baseGrid, guess) ->
              Grid.unpartitionSep baseGrid pData guess

      -- TODO: ugly to separate these but the needs are slightly different
      choice "partitionSepIO" [
        ("projectUniform", do
            -- TODO: project only one side? or only if downscale wouldn't apply?
            guard $ all (uncurry Grid.allSameDims) (zip (Ex.train pInputs) pOutputs)
            newInputs  <- liftO $ Ex.mapM (\pInput -> Grid.fromFuncM (Box.dims pInput) (\idx -> Grid.isUniform (Box.get pInput idx))) pInputs
            newOutputs <- liftO $ mapM (\pOutput -> Grid.fromFuncM (Box.dims pOutput) (\idx -> Grid.isUniform (Box.get pOutput idx))) pOutputs

            pop 1 $ do
              let reconstructG2GG guesses = flip mapM (zip (Ex.test pInputs) guesses) $ \(pInput, guess) -> do
                    unless (Box.dims pInput == Grid.dims guess) $ do
                      liftIO . traceIO $ "[projectUniform] reconstruct failed " ++ show (Box.dims pInput, Grid.dims guess)
                    guard (Box.dims pInput == Grid.dims guess)
                    pure $ Box.fromFunc (Box.dims pInput) $ \idx ->
                      Grid.const (Grid.dims $ Box.get pInput idx) (Grid.get guess idx)
              let reconstruct guesses = reconstructG2GG guesses >>= (MaybeT . pure . reconstructGG2G)

              pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) reconstruct),
        ("projectUniformO", do
            guard $ all (uncurry Grid.allSameDims) (zip (Ex.train pInputs) pOutputs)
            -- Only the outputs need to be uniform (so we can reconstruct)
            newOutputs <- liftO $ mapM (\pOutput -> Grid.fromFuncM (Box.dims pOutput) (\idx -> Grid.isUniform (Box.get pOutput idx))) pOutputs

            -- TODO: generic group support (i.e. most frequently occuring color)
            grid2color <- runSynth11 ctx $ do
              grid2color :: Grid Color -> Color <- enumListValueMaps blank (pure $ Grid.toList)
              -- TODO: could relax with heuristic
              guard $ flip any (zip newOutputs (Ex.train pInputs)) $ \(newOutput, pInput) ->
                Dims.any (Grid.dims newOutput) $ \idx -> nonBlank (grid2color $ Box.get pInput idx)

              guard $ flip any (zip newOutputs (Ex.train pInputs)) $ \(newOutput, pInput) ->
                Dims.all (Grid.dims newOutput) $ \idx ->
                  let c = grid2color (Box.get pInput idx) in
                    (nonBlank c) <= (c == Grid.get newOutput idx)

              pure grid2color

            let newInputs = Ex.map (\pInput -> Grid.fromFunc (Box.dims pInput) (\idx -> grid2color (Box.get pInput idx))) pInputs

            let reconstructG2GG guesses = flip mapM (zip (Ex.test pInputs) guesses) $ \(pInput, guess) -> do
                  unless (Box.dims pInput == Grid.dims guess) $ do
                    liftIO . traceIO $ "[projectUniform] reconstruct failed " ++ show (Box.dims pInput, Grid.dims guess)
                  guard (Box.dims pInput == Grid.dims guess)
                  pure $ Box.fromFunc (Box.dims pInput) $ \idx ->
                    Grid.const (Grid.dims $ Box.get pInput idx) (Grid.get guess idx)
            let reconstruct guesses = reconstructG2GG guesses >>= (MaybeT . pure . reconstructGG2G)

            pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) reconstruct),

        -- TODO: allow solveGG2GG to return a regular subproblem, and handle the reconstruction
        -- Motivation: 272f95fa
        ("trySolveGG2GG", do
            nestedGuesses <- trySolveGG2GG $ Goal pInputs pOutputs newCtx
            guesses <- liftO $ reconstructGG2G nestedGuesses
            pure . TacticResult.Guess $ guesses),

        ("unpartitionNoSep", do
            guard $ pSepKind == SepEven
            rpDatas <- liftO $ do
              let pOutput0 = head pOutputs
              if all (\pOutput -> Grid.allSameDims pOutput0 pOutput) pOutputs
                then mapM (\_ -> Grid.computeRePartitionData pOutput0) (Ex.test pInputs)
                else if all (\(pInput, pOutput) -> Grid.allSameDims pInput pOutput) (zip (Ex.train pInputs) pOutputs)
                     then mapM Grid.computeRePartitionData (Ex.test pInputs)
                     else Nothing
            let reconstruct :: ForTrain (Grid Color) -> MaybeT IO (ForTrain (Grid Color))
                reconstruct gGuesses = do
                  ggGuesses :: ForTrain (Box.Grid (Grid Color)) <- MaybeT . pure $ mapM (\(rpData, guess) -> Grid.rePartitionNoSepWith guess rpData) (zip rpDatas gGuesses)
                  guesses   :: ForTrain (Grid Color)        <- MaybeT . pure $ reconstructGG2G ggGuesses
                  pure guesses
            newInputs  <- liftO $ Ex.mapM Grid.unpartitionNoSep pInputs
            newOutputs <- liftO $ mapM Grid.unpartitionNoSep pOutputs
            pure $ TacticResult.Decompose (Goal newInputs newOutputs newCtx) reconstruct),

        ("splitGG2GG", splitGG2GG (\gs -> MaybeT . pure $ reconstructGG2G gs) $ Goal pInputs pOutputs newCtx)
        ]

    partitionSepI pSepKind pInputsColors pInputs newCtx = do
      choice "partitionSepI" [
        ("projectNonBlank", do
            newInputs :: Ex (Grid Color) <- liftO $ flip Ex.mapM pInputs $ \pInput -> do
              b :: Box.Grid (Grid Color) <- Box.fromFuncM (Box.dims pInput) $ \idx -> do
                let g :: Grid Color = Box.get pInput idx
                rect :: Rect <- Grid.nonBlankRect g
                pure $ Grid.getRect g rect
              Grid.unpartitionNoSep b
            guard $ newInputs /= inputs
            guard $ all (uncurry Grid.sameDims) (zip (Ex.train newInputs) outputs)
            pure $ TacticResult.Decompose (Goal newInputs outputs newCtx) pure)
        , ("projectUniform", do
              newInputs  <- liftO $ Ex.mapM (\pInput -> Grid.fromFuncM (Box.dims pInput) (\idx -> Grid.isUniform (Box.get pInput idx))) pInputs
              pure $ TacticResult.Decompose (Goal newInputs outputs newCtx) pure)
        , ("trySolveGG2G", trySolveGG2G $ Goal pInputs outputs newCtx)
        , ("unpartitionNoSep", do
               guard $ pSepKind == SepEven
               newInputs <- liftO $ Ex.mapM Grid.unpartitionNoSep pInputs
               pure $ TacticResult.Decompose (Goal newInputs outputs newCtx) pure)
        , ("splitGG2G", splitGG2G $ Goal pInputs outputs newCtx)
        ]

partitionEven :: StdGoal -> SolveM TacticResult
partitionEven goal = choice "partitionEven" [
  ("partitionEvenI", partitionEvenI goal),
  ("bitmaskTileO",   bitmaskTileO goal)
  ]
  where
    partitionEvenI goal@(Goal inputs outputs ctx) = do
      let ratios :: [(Ratio Int, Ratio Int)] = map (\(input, output) ->
                                                      -- Note: this looks like `mod` but is actually `div` for some crazy reason
                                                      (Grid.nRows input % Grid.nRows output, Grid.nCols input % Grid.nCols output))
                                               (zip (Ex.train inputs) outputs)

      -- TODO: weaker guards
      guard $ allSame . map fst $ ratios
      guard $ allSame . map snd $ ratios
      guard $ any (\(rr, cc) -> numerator rr /= 1 || numerator cc /= 1) ratios
      guard $ all (\(rr, cc) -> denominator rr == 1 && denominator cc == 1) ratios

      let newDims = Dims (numerator . fst . head $ ratios) (numerator . snd . head $ ratios)
      -- TODO: these may be the same, and we don't want to repeat ourselves
      choice "partitionEvenI" [
        ("inner", do
            pInputs <- liftO $ Ex.mapM (Grid.partitionEvenInnerDims newDims) inputs
            trySolveGG2G $ Goal pInputs outputs ctx),
        ("outer", do
            pInputs <- liftO $ Ex.mapM (Grid.partitionEvenOuterDims newDims) inputs
            trySolveGG2G $ Goal pInputs outputs ctx),
        ("innerSplit", do
            pInputs <- liftO $ Ex.mapM (Grid.partitionEvenInnerDims newDims) inputs
            splitGG2G $ Goal pInputs outputs ctx),
        ("outerSplit", do
            pInputs <- liftO $ Ex.mapM (Grid.partitionEvenOuterDims newDims) inputs
            splitGG2G $ Goal pInputs outputs ctx)
        ]

    -- TODO: we really want to create multiple subgoals! Might not be that big of a refactor!
    bitmaskTileO goal@(Goal inputs outputs ctx) = do
      outputsGG :: ForTrain (Box.Grid (Grid Color)) <- liftO $ flip mapM (zip (Ex.train inputs) outputs) $ \(input, output) ->
        Grid.partitionEven (Grid.dims input) (Grid.dims input) output
      tiles :: ForTrain (Grid Color) <- flip mapM outputsGG $ \outputGG -> do
        let nbs = filter (not . Grid.allBlank) . Box.toList $ outputGG
        guard . not . null $ nbs
        guard $ List.allSame nbs
        pure $ head nbs

      let tileGoal :: StdGoal = Goal inputs tiles ctx
      testTiles :: ForTest (Grid Color) <- solveTileGoal 1 tileGoal

      -- TODO: this is weird.
      let projectColors :: ForTrain Color =
            if all (\g -> Grid.nDistinctVals nonBlank g == 1) tiles
            then map (Maybe.fromJust . Grid.firstVal nonBlank) tiles
            else map (\_ -> Color 1) tiles -- TODO: colorTrue causing issues downstream

      let newOutputs = flip map (zip projectColors outputsGG) $ \(c, outputGG) -> Grid.fromFunc (Box.dims outputGG) $ \idx ->
            let x = Box.get outputGG idx in
              if Grid.allBlank x then blank else c

      let reconstruct guesses = flip mapM (zip guesses testTiles) $ \(guess, tile) ->
            Grid.unpartitionEven $ Box.fromFunc (Grid.dims guess) $ \idx ->
              let x = Grid.get guess idx in
                if isBlank x
                then Grid.const (Grid.dims guess) blank
                else tile

      pure $ TacticResult.Decompose (goal { outputs = newOutputs }) (MaybeT . pure . reconstruct)

    -- TODO: obviously should just return 2 subgoals to the main solveGoal
    solveTileGoal :: Int -> StdGoal -> SolveM (ForTest (Grid Color))
    solveTileGoal fuel tileGoal
      | fuel == 0 = do
          TacticResult.Guess tiles <- identity tileGoal
          pure tiles
      | fuel > 0  = do
          tacticResult <- choice "solveTileGoal" [
            ("identity",        identity tileGoal),
            ("colorMap",        colorMap tileGoal),
            ("inputSymmetries", inputSymmetries tileGoal),
            ("colorBlast",      colorBlast tileGoal)
            ]
          case tacticResult of
            TacticResult.Guess tiles -> pure tiles
            TacticResult.Decompose newTileGoal reconstruct -> do
              nestedGuesses <- solveTileGoal (fuel-1) newTileGoal
              guesses <- liftIO . runMaybeT $ reconstruct nestedGuesses
              liftO guesses
