-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Solver.Tactics.ShapeMap where

import Util.Imports
import qualified Util.List as List
import qualified Data.List as List
import Solver.SolveM
import qualified Solver.Goal
import Search.SearchT
import qualified Synth.Ex as Ex
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Lib.Grid as Grid
import qualified Lib.Index as Index
import qualified Lib.Rect as Rect
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Util.Map as Map
import Lib.Axis
import Lib.Index (Index(Index))
import Synth1.Basic
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
import Lib.Blank
import Search.DFS
import Lib.Shape (Shape)
import qualified Solver.ArcContext as ArcContext
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
import qualified Solver.Synth1Context as Synth1Context
import Solver.Synth1Context (Synth1Context(..))
import Solver.ArcContext
import qualified Lib.Direction as Direction
import Lib.Direction (Direction)
import Solver.Goal
import Synth.Basic
import qualified Synth.Spec as Spec
import qualified Synth.Spec.ESpec as ESpec
import Synth.Spec
import Synth.Spec.ESpec
import Synth.Core
import Synth.Context
import Synth.Bool
import Synth.EagerFeatures
import Synth.LazyFeatures
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.Spec.USpec
import Synth.Sequence
import qualified Synth.Bool as DListOptions
import Lib.Features
import Lib.Synth

type ShapeC = Shape Color
type ShapeMap = Map ShapeC ShapeC

data ShapeMapOptions = ShapeMapOptions {
  maxShapesPerExample :: Int,
  minBlanksPerExample :: Int,
  maxFuelPerTraining  :: Float
  } deriving (Eq, Ord, Show)

defaultShapeMapOptions = ShapeMapOptions {
  maxShapesPerExample = 20,
  minBlanksPerExample = 2,
  maxFuelPerTraining  = 0.66
  }

shapeMap :: Solver.Goal.StdGoal -> SolveM TacticResult
shapeMap goal@(Solver.Goal.Goal inputs outputs ctx) = do
  choice "shapeMap" [
    ("shapes2shapes", tacticShapes2Shapes goal),
    ("selectSpecial", tacticSelectSpecial goal)
    ]

tacticShapes2Shapes :: StdGoal -> SolveM TacticResult -- TODO: the find1 is very questionable!
tacticShapes2Shapes goal@(Goal inGrids outGrids ctx) = find1 "shapeMap::shape2shape" $ do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inGrids) outGrids)
  guard $ all ((>= (minBlanksPerExample defaultShapeMapOptions)) . Grid.nBlanks) inGrids

  dOpts <- oneOf "dOpts" $
    concatMap (\fuel -> [("strict:" ++ show fuel, strictOpts fuel), ("relaxed:" ++ show fuel, relaxedOpts fuel)]) [0, 1, 2]
    ++ map (\fuel -> ("strict:" ++ show fuel, strictOpts fuel)) [3, 4]

  allParseAlignments :: [Guess (Ex [ShapeC], ForTrain [Maybe ShapeC])] <- lift . enumAllG $ do
    ParseResult inShapes outShapes <- enumParses goal [
      Parse.Options   { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksAny }
      , Parse.Options { Parse.kind = Parse.ParseLocalNone,  Parse.color = Parse.ParseNoBlanksByColor }
      ]

    guard $ all ((<= (maxShapesPerExample defaultShapeMapOptions)) . length) inShapes

    outShapes :: ForTrain [Maybe ShapeC] <- enumAlignments (Ex.train inShapes) outShapes [
      AlignShapes.RevAlignPoint2Shape 4
      , AlignShapes.Shape2ShapeIntersectsUnique AlignShapes.ColorsNeedNotMatch
      , AlignShapes.Shape2ShapeIntersectsUnique AlignShapes.ColorsMustMatch
      , AlignShapes.RevAlignPoint2Shape 0
      ]
    pure (inShapes, outShapes)

  -- Note: the score function below could be simplified now that we require closer-parses
  let closerAlignments = flip filter allParseAlignments $ \(Guess (_, outShapes) _ _ _) ->
        nOutputPointsUnexplained outGrids outShapes == 0

  (inShapes, outShapes) <- oneOf "ParseAlignment" $ sortUniqueParseAlignments goal closerAlignments
  guard $ any (any Maybe.isJust) outShapes
  guard $ flip any (zip (Ex.train inShapes) outShapes) $ \(s1, s2) -> map Just s1 /= s2

  guesses :: Ex [Maybe ShapeC] <- do
    let actx = ArcContext (EagerFeatures . ctxInts $ ctx) (EagerFeatures . ctxColors $ ctx)
    synthShapes2Shapes dOpts $ ESpec (Ex.getInfo inShapes) (inShapes, (inGrids, actx)) outShapes

  sanityCheckSynth guesses outShapes

  let newInGrids = flip Ex.map (Ex.zip3 inGrids inShapes guesses) $ \(inGrid, inShapes, guesses) ->
        Grid.replacingShapes inGrid inShapes (map Maybe.fromJust . filter Maybe.isJust $ guesses)

  pure $ TacticResult.Decompose (goal { Solver.Goal.inputs = newInGrids }) pure

  where
    sortUniqueParseAlignments :: StdGoal -> [Guess (Ex [ShapeC], ForTrain [Maybe ShapeC])] -> [Choice (Ex [ShapeC], ForTrain [Maybe ShapeC])]
    sortUniqueParseAlignments goal parses =
      let uniqSorted :: [Guess (Ex [ShapeC], ForTrain [Maybe ShapeC])] = List.stableUniqKey Guess.value $ List.sortOn (score goal) parses in
        map (\guess -> (History.showCondensed (Guess.history guess), Guess.value guess)) uniqSorted

    score (Goal inputs outputs _) (Guess (inShapes, outShapes) _ _ _) = (nOutputPointsUnexplained outputs outShapes, sum (map length outShapes))

    nOutputPointsUnexplained outputs outShapes = sum . flip map (zip outputs outShapes) $ \(output, outShapes) ->
      Grid.nNonBlankVals output - sum (map (\s -> case s of Nothing -> 0; Just s -> Shape.nPoints s) outShapes)

data ShapesFeatures = ShapesFeatures {
  sfBools   :: EagerFeatures [Bool],
  sfInts    :: EagerFeatures [Int],
  sfColors  :: EagerFeatures [Color],
  sfShapes  :: EagerFeatures [ShapeC],
  sfMShapes :: EagerFeatures [Maybe ShapeC]
  }

computeShapeFeatures :: Ex (Grid Color) -> Ex [ShapeC] -> ArcContext -> CoreM ShapesFeatures
computeShapeFeatures inGrids {- unnormalized -} inShapes actx = do
  maybeShapeFeaturesSeq <- precompute $ do
    shapes2maybeShapes <- oneOf "maybeShapeFeaturesSeq" [
      ("uniqueTouching",                Shape.uniqueTouchingShape)
      , ("uniqueNearestSpecial",        Shape.uniqueNearestShapeSpecial)
      , ("uniqueSameNormalizedIndices", Shape.uniqueSameNormalizedIndices)
      , ("minContainer",                Shape.minShapeContainer)
      , ("maxContainer",                Shape.maxShapeContainer)
      , ("minContained",                Shape.smallestInShape)
      , ("maxContained",                Shape.biggestInShape)
      ]
    bits <- oneOf "bits" [("colors", id), ("bits", Shape.fill colorTrue)]
    pure $ flip Ex.map inShapes $ \inShapes ->
      map (fmap $ bits . Shape.normalize) (shapes2maybeShapes inShapes)

  intFeaturesSeq <- precompute $ do
    shape2int <- enumIntFeatures
    choice "intFeatures" [
      ("independent", pure $ Ex.map (map shape2int) inShapes),
      ("ranks",       pure $ Ex.map (List.indexInSorted . map shape2int) inShapes)
      ]

  boolFeaturesSeq <- precompute $ do
    bools :: Ex [Bool] <- choice "boolFeaturesSeq" [
      ("standard", do
          shapes2bools <- choice "enumAllGroupBoolFeatures" [
            -- TODO: put this in all of the group bool things
            --   - it is a better prior than having an int feature being unique
            ("shapeCounts",       enumCountFeatures . pure $ \(s :: ShapeC) -> Set.fromList [Shape.normalize s])
            , ("shapeBitCounts",  enumCountFeatures . pure $ \(s :: ShapeC) -> Set.fromList [Shape.discardValues (Shape.normalize s)])
            , ("2bool",           do { phi2bool <- enumBoolFeatures; pure $ \xs -> Prelude.map phi2bool xs })
            , ("shapeRectCounts", enumCountFeatures . pure $ \(s :: ShapeC) -> Set.fromList [Shape.enclosingRect (Shape.normalize s)])
            , ("group2set2bool",  enumGroupSetBoolFeatures Shape.enumSetFeatures)
            ]
          pure $ Ex.map shapes2bools inShapes)
      , ("maybeShapeFeatures", do
            maybeShapes <- oneOf "maybeShape" maybeShapeFeaturesSeq
            pure $ Ex.map (map Maybe.isJust) maybeShapes)
      , ("isTouchingUniform", do
            c <- enumVals
            pure $ Ex.map (Shape.isTouchingShapeUniformVal c) inShapes)
      , ("risky", do
            -- the not-normalized path is motivated by ed74 (max minCol)
            shapes2bools <- enumGroupIntBoolFeatures
            norm <- oneOf "normalize" [("yes", Shape.normalize), ("no", id)]
            pure $ Ex.map (shapes2bools . map norm) inShapes)
      , ("riskyNorm", do
            phi2int2bool <- enumIntBoolFeatures
            pure $ Ex.map (map $ phi2int2bool . Shape.normalize) inShapes)
      ]
    neg <- choice "negate" [("no", pure id), ("yes", pure not)]
    pure $ Ex.map (map neg) bools

  colorFeaturesSeq <- precompute $ choice "colorFeaturesSeq" [
    ("majority", pure $ Ex.map (map (List.mostCommon . Shape.valuesToList)) inShapes)
    , ("minority", pure $ Ex.map (map (List.leastCommon . Shape.valuesToList)) inShapes)
    -- TODO: this is a bit of a hack, there are much more general ways of handling this kind of thing
    , ("majorityOfMShape", do
          mShapes :: Ex [Maybe ShapeC] <- oneOf "maybeShapeFeaturesSeq" maybeShapeFeaturesSeq
          pure $ flip Ex.map mShapes $ \mShapes -> flip map mShapes $ \mShape ->
            case mShape of
              Nothing -> blank
              Just s -> Shape.majorityVal s)
    ]

  colorFeaturesCtx <- precompute $ choice "colorFeaturesCtx" [
    ("shapeColor", do
        f <- oneOf "mostOrLeast" [("most", List.mostCommon), ("least", List.leastCommon)]
        flip Ex.mapM inShapes $ \inShapes -> do
          colors <- liftO $ mapM Shape.uniformColorOpt inShapes
          guard $ not (null colors)
          pure $ f colors)
    , ("gridColor", do
          f <- oneOf "mostOrLeast" [("most", Grid.majorityNonBlankVal), ("least", Grid.minorityNonBlankVal)]
          Ex.mapM (liftO . f) inGrids)
    , ("ctx",
       oneOf "ctx" $ EagerFeatures.choices (ArcContext.colors actx))
    ]

  shapeFeaturesCtx <- precompute $ do
    bs <- oneOf "boolFeatures" boolFeaturesSeq
    bits <- oneOf "bits" [("colors", id), ("bits", Shape.fill colorTrue)]
    flip Ex.mapM (Ex.zip bs inShapes) $ \(bs, inShapes) -> do
      let specials = map snd . filter fst $ zip bs inShapes
      guard $ length specials == 1
      pure . Shape.normalize . bits . head $ specials

  let broadcast flatThings = flip map flatThings $ \(n, flatThing) -> (n, flip Ex.map (Ex.zip inShapes flatThing) $ \(inShapes, x) -> replicate (length inShapes) x)

  pure $ ShapesFeatures {
    sfBools     = EagerFeatures boolFeaturesSeq
    , sfInts    = EagerFeatures intFeaturesSeq
    , sfColors  = EagerFeatures $ colorFeaturesSeq ++ broadcast colorFeaturesCtx
    , sfShapes  = EagerFeatures $ broadcast shapeFeaturesCtx
    , sfMShapes = EagerFeatures $ maybeShapeFeaturesSeq
    }

data Shape2ShapeCtx = Shape2ShapeCtx {
  ssInputs  :: Ex ShapeC,
  ssIndices :: Ex Int,
  ssInts    :: EagerFeatures Int,
  ssColors  :: EagerFeatures Color,
  ssShapes  :: EagerFeatures ShapeC,
  ssMShapes :: EagerFeatures (Maybe ShapeC)
  }

shapesFeaturesToShape2ShapeCtx :: Ex [ShapeC] -> ShapesFeatures -> (EagerFeatures Bool, Shape2ShapeCtx, Ex (Maybe ShapeC) -> Ex [Maybe ShapeC])
shapesFeaturesToShape2ShapeCtx shiftedInShapes (ShapesFeatures sfBools sfInts sfColors sfShapes sfMShapes) =
  let (flatInputs, unflatten) = Ex.flatten shiftedInShapes
      shape2shapeCtx = Shape2ShapeCtx {
        ssInputs    = flatInputs
        , ssIndices = Ex.flatProvenance shiftedInShapes
        , ssInts    = flatten sfInts
        , ssColors  = flatten sfColors
        , ssShapes  = flatten sfShapes
        , ssMShapes = flatten sfMShapes
        }
  in
    (flatten sfBools, shape2shapeCtx, unflatten)
  where
    flatten (EagerFeatures choices) = EagerFeatures $ fmap (onSndWith $ fst . Ex.flatten) choices

instance SynthContext Shape2ShapeCtx where
  partitionOn b (Shape2ShapeCtx inputs indices ints colors shapes maybeShapes) =
    let (inputs1,  inputs2)  = partitionOn b inputs
        (indices1, indices2) = partitionOn b indices
        (ints1,    ints2)    = partitionOn b ints
        (colors1,  colors2)  = partitionOn b colors
        (shapes1,  shapes2)  = partitionOn b shapes
        (mShapes1, mShapes2) = partitionOn b maybeShapes
    in
      (Shape2ShapeCtx inputs1 indices1 ints1 colors1 shapes1 mShapes1,
       Shape2ShapeCtx inputs2 indices2 ints2 colors2 shapes2 mShapes2)


synthShapes2Shapes :: DListOptions -> SynthFn CoreM ESpec (Ex [ShapeC], (Ex (Grid Color), ArcContext)) [Maybe ShapeC]
synthShapes2Shapes dOpts spec@(ESpec _ (unnormalizedInShapes, (inGrids, actx)) unnormalizedOutShapes) = do
  shapesFeatures <- lift $ computeShapeFeatures inGrids unnormalizedInShapes actx
  (inShapes, outShapes, unshift) <- shiftShapes unnormalizedInShapes unnormalizedOutShapes

  let (boolFeatures, s2sContext, unflatten) = shapesFeaturesToShape2ShapeCtx inShapes shapesFeatures
  let flatOutputs = concat outShapes

  -- TODO: put before the computation
  -- 0.66
  -- 2 train --> 0
  -- 3 train --> 0
  -- 4 train --> 1
  -- 5 train --> 2
  guard $ fromIntegral (DListOptions.initialFuel dOpts) + 1 < fromIntegral (length (Ex.train $ ssInputs s2sContext)) * maxFuelPerTraining defaultShapeMapOptions

  flatGuesses <- decisionList dOpts (synthShapeTransform 2) $ ESpec (Ex.getInfo (ssInputs s2sContext)) (boolFeatures, s2sContext) flatOutputs
  sanityCheckSynth flatGuesses flatOutputs
  pure $ unshift $ unflatten flatGuesses

synthShapeTransform :: Integer -> SynthFn CoreM ESpec Shape2ShapeCtx (Maybe ShapeC)
synthShapeTransform fuel spec = do
  --liftIO . traceIO $ "[synthShapeTransform] " ++ show fuel ++ " " ++ show (ESpec.labels spec)
  choice "synthShapeTransform" [
    ("nothings", do
        guard $ all Maybe.isNothing (ESpec.labels spec)
        constValueE spec),
    ("justs",    do
        spec <- unpackMaybes spec
        guesses <- core fuel spec
        pure $ Ex.map Just guesses)
    ]
  where
    unpackMaybes (ESpec info ctx labels) = do
      guard $ all Maybe.isJust labels
      pure $ ESpec info ctx (map Maybe.fromJust labels)

    core fuel spec
      | fuel == 0 = basecase spec
      | otherwise = choice "synthShapeTransform" [
          ("basecase", basecase spec),
          ("backup", do
              (newSpec, reconstruct) <- choice "backup" [
                ("nailTheColors",     nailTheColors spec)
                , ("updateAlignment", updateAlignment spec)
                , ("fillRectWith",    fillRectWith spec)
                , ("frameRectWith",   frameRectWith spec)
                , ("maxSubRect",      maxSubRect spec)
                --, ("cropMajority",    cropMajority spec)
                ]
              guesses <- core (fuel-1) newSpec
              liftO . reconstruct $ guesses)
          ]

    basecase (ESpec info ctx labels) = choice "basecase" [
        ("identity",       identityP    $ ESpec info (ssInputs ctx) labels),
        ("constant",       constValueE  $ ESpec info () labels),
        ("shapeFeature", do
            (n, shape) <- oneOfS "shape" $ EagerFeatures.choices (ssShapes ctx)
            identityP $ ESpec info shape labels),
        ("lookupTable",    lookupTableE $ ESpec info (ssInputs ctx) labels),
        ("swaps",          synthSwaps $ ESpec info (ssInputs ctx, ssIndices ctx) labels)
        ]

    shape2color (ESpec info ctx labels) = choice "shape2color" [
        ("identity",       focusing identityP $ ESpec info (ssColors ctx) labels),
        ("constant",       constValueE  $ ESpec info () labels),
        -- TODO: try this everywhere?
        ("tryIfEq",        focusing tryIfEq  $ ESpec info (ssInts ctx) labels),
        -- TODO: have this option everywhere? (e.g. in the basecase above?)
        ("lookupTableMShape", do
            (n, mShapes) <- oneOfS "mShape" $ EagerFeatures.choices (ssMShapes ctx)
            --liftIO . traceIO $ "[lookupTableMShape] " ++ show n ++ " " ++ show (zip (take 4 $ Ex.train mShapes) labels)
            lookupTableE $ ESpec info mShapes labels),
        -- TODO: ranks only?
        -- TODO: have this option everywhere? (e.g. in the basecase above?)
        ("lookupTableInt", focusing lookupTableE $ ESpec info (ssInts ctx) labels)
        ]

    nailTheColors (ESpec info ctx labels) = do
      outColors     :: ForTrain Color <- flip mapM labels $ liftO . Shape.uniformColorOpt
      fillColors    :: Ex Color       <- find1 "nailTheColors" . shape2color $ ESpec info ctx outColors
      -- We set the labels to be a uniform color (so lookup/const can apply)
      let newInputs :: Ex ShapeC       = Ex.map (Shape.fill colorTrue) (ssInputs ctx)
      let newLabels :: ForTrain ShapeC = map (Shape.fill colorTrue) labels

      let newShapes = flip map (EagerFeatures.choices (ssShapes ctx)) $ \(n, s) -> (n, Ex.map (Shape.fill colorTrue) s)
      guard $ newInputs /= newInputs || newLabels /= labels
      let reconstruct guesses = pure $ Ex.map (uncurry Shape.fill) (Ex.zip fillColors guesses)
      pure $ (ESpec info (ctx { ssInputs = newInputs }) newLabels, reconstruct)

    -- TODO: this can try shifting the input shape to see if it "lines up better"
    -- Actually, could the entire diffIdx thing be subsumed here??
    updateAlignment (ESpec info ctx labels) = deadend ""

    fillRectWith (ESpec info ctx@(Shape2ShapeCtx inputs idxs ints colors shapes maybeShapes) labels) = do
      fillColors <- liftO $ mapM (uncurry Shape.isResultOfFillRect) (zip (Ex.train inputs) labels)
      let fillRectDeltas = flip map (zip (Ex.train inputs) labels) $ \(input, label) ->
            Shape.enclosingRect label - Shape.enclosingRect input

      guessColors     :: Ex Color <- find1 "colors"     . focusing synthBasecase $ ESpec info colors fillColors
      guessRectDeltas :: Ex Rect <-  find1 "rectDeltas" . synthInts2Rect         $ ESpec info ints fillRectDeltas

      let newInputs :: Ex ShapeC = flip Ex.map (Ex.zip3 guessColors guessRectDeltas inputs) $ \(c, rDelta, s) ->
            Shape.fillRectWith c (Shape.enclosingRect s + rDelta) s

      guard $ newInputs /= inputs
      pure (ESpec info (ctx { ssInputs = newInputs }) labels, pure)

    frameRectWith (ESpec info ctx labels) = do
      outColors   <- liftO $ mapM (uncurry Shape.isResultOfFrameRect) (zip (Ex.train (ssInputs ctx)) labels)
      guessColors <- find1 "frameRectWith" . shape2color $ ESpec info ctx outColors
      let newInputs = flip Ex.map (Ex.zip guessColors (ssInputs ctx)) $ uncurry Shape.frameRectWith
      guard $ newInputs /= ssInputs ctx
      checksum <- lift $ asks ctxChecksum
      pure (ESpec info (ctx { ssInputs = newInputs}) labels, pure)

    maxSubRect spec@(ESpec info ctx labels) = do
      guard $ all Shape.isFilledRect labels
      let inputs = ssInputs ctx
      guard $ all (uncurry Shape.subsetMatches) (zip labels (Ex.train inputs))
      guard $ all (\(s1, s2) -> Shape.nPoints s1 >= Shape.nPoints s2) (zip (Ex.train inputs) labels)
      guard $ any (\(s1, s2) -> Shape.nPoints s1 >  Shape.nPoints s2) (zip (Ex.train inputs) labels)

      guesses <- flip Ex.mapM inputs $ \s -> do
        let or = Shape.maxSubRect s
        r <- liftO or
        pure $ Shape.filter (Rect.containsIndex r) s
      guard $ guesses /= inputs
      -- to be a closer, uncomment:
      -- guard $ all (uncurry (==)) (zip (Ex.train guesses) shapeLabels)
      pure (ESpec info (ctx { ssInputs = guesses}) labels, pure)

{-
    backupCropMajority :: SynthFn1 CoreM ESpec (Ex ShapeC, ArcContext) ShapeC ESpec (Ex ShapeC, ArcContext) ShapeC
    backupCropMajority spec@(ESpec info (specialShapes, actx) shapeLabels) = do
      guard $ all (uncurry Shape.subsetMatches) (zip shapeLabels (Ex.train specialShapes))
      guard $ all Shape.isUniform shapeLabels
      guard $ any (not . Shape.isUniform) (Ex.train specialShapes)
      guard $ all (\(s1, s2) -> Shape.nPoints s1 >= Shape.nPoints s2) (zip (Ex.train specialShapes) shapeLabels)
      guard $ any (\(s1, s2) -> Shape.nPoints s1 >  Shape.nPoints s2) (zip (Ex.train specialShapes) shapeLabels)

      let guesses = Ex.map Shape.cropToMajorityVal specialShapes
      guard $ guesses /= specialShapes
      guard $ all (uncurry (==)) (zip (Ex.train guesses) shapeLabels)
      pure (ESpec info (guesses, actx) shapeLabels, pure)

    -- monochromatically framed
    isFramed :: Shape Color -> Maybe Color
    isFramed shape = do
      c <- List.iterM (Rect.getPerimeterIdxs . Shape.enclosingRect $ shape) blank $ \acc idx -> do
        val <- Shape.getOpt shape idx
        if isBlank acc then pure val else guard (acc == val) *> pure acc
      guard $ nonBlank c
      pure c

-}


tacticSelectSpecial :: StdGoal -> SolveM TacticResult -- TODO: the find1 is questionable!
tacticSelectSpecial goal@(Goal inputs outputs ctx) = find1 "shapeMap::selectSpecial" $ do
  let actx :: ArcContext = ArcContext (EagerFeatures (ctxInts ctx)) (EagerFeatures (ctxColors ctx))

  ParseResult pInputs pOutputs <- enumUniqueParses goal [
    Parse.Options { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksByColor },
    Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor },
    Parse.Options { Parse.kind = Parse.ParseLocalAny,   Parse.color = Parse.ParseNoBlanksAny },
    Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksAny }
    ]

  outShapes :: ForTrain ShapeC <- flip mapM pOutputs $ \pOutput -> do { guard $ length pOutput == 1; pure . head $ pOutput }

  shapesFeatures <- lift $ computeShapeFeatures inputs pInputs actx

  (n, bs) <- oneOfS "specialBool" $ EagerFeatures.choices (sfBools shapesFeatures)

  s2sCtx <- liftO $ do
    inputs  <- selectCtx bs (Ex.map (map Shape.normalize) pInputs)
    ints    <- selectCtx bs (sfInts shapesFeatures)
    colors  <- selectCtx bs (sfColors shapesFeatures)
    shapes  <- selectCtx bs (sfShapes shapesFeatures)
    mShapes <- selectCtx bs (sfMShapes shapesFeatures)
    let idxs = Ex (map fst (zip [0..] (Ex.train inputs))) (map fst (zip [(length (Ex.train inputs))..] (Ex.test inputs)))
    pure $ Shape2ShapeCtx inputs idxs ints colors shapes mShapes

  shapeGuesses :: Ex (Maybe ShapeC) <- find1 "synthShape2Shape" $ synthShapeTransform 1 $ ESpec (Ex.getInfo inputs) s2sCtx (map Just outShapes)
  sanityCheckSynth shapeGuesses (map Just outShapes)
  guard $ Ex.all Maybe.isJust shapeGuesses

  let guesses :: ForTest (Grid Color) = flip map (map Maybe.fromJust $ Ex.test shapeGuesses) $ \testShape ->
        Grid.fromShapes (Rect.dims $ Shape.enclosingRect testShape) [testShape]
  pure $ TacticResult.Guess guesses

sanityCheckSynth :: (Eq a, Show a) => Ex a -> ForTrain a -> SolveM ()
sanityCheckSynth guesses labels = unless (Ex.train guesses == labels) $ do
  liftIO . traceIO $ "[shapeMap] exact spec contract violated!!"
  liftIO . traceIO $ "[shapeMap] labels:  " ++ show labels
  liftIO . traceIO $ "[shapeMap] guesses: " ++ show (Ex.train guesses)
  error "[shapeMap] contract violated"


{---------------------------------------------------}
{- Buried at the end because I hate looking at it. -}
{---------------------------------------------------}

-- TODO: make this a normal backup operator, so we compute features for the unnormalized shapes
shiftShapes :: Ex [ShapeC] -> ForTrain [Maybe ShapeC] -> SolveM (Ex [ShapeC], ForTrain [Maybe ShapeC], Ex [Maybe ShapeC] -> Ex [Maybe ShapeC])
shiftShapes pInputs pOutputs = do
  let shape2shape2idxDiffs inShape outShape =
        case outShape of
          Nothing -> (Index 0 0, Index 0 0)
          Just outShape ->
            let inRect    = Shape.enclosingRect inShape
                outRect   = Shape.enclosingRect outShape
                unionRect = Rect.union inRect outRect
                rDiffIn   = Index.row (Rect.upperLeft inRect)  - Index.row (Rect.upperLeft unionRect)
                cDiffIn   = Index.col (Rect.upperLeft inRect)  - Index.col (Rect.upperLeft unionRect)
                rDiffOut  = Index.row (Rect.upperLeft outRect) - Index.row (Rect.upperLeft unionRect)
                cDiffOut  = Index.col (Rect.upperLeft outRect) - Index.col (Rect.upperLeft unionRect)
            in
              (Index rDiffIn cDiffIn, Index rDiffOut cDiffOut)

  shape2diffMap :: Map ShapeC Index <- List.iterM (zip (Ex.train pInputs) pOutputs) Map.empty $ \acc (inShapes, outShapes) ->
        List.iterM (zip inShapes outShapes) acc $ \acc (inShape, outShape) -> do
          let nShape       = Shape.normalize inShape
          let (idxDiff, _) = shape2shape2idxDiffs inShape outShape
          case Map.lookup nShape acc of
            Nothing -> pure $ Map.insert nShape idxDiff acc
            Just idx -> do { guard (idx == idxDiff); pure acc }

  (trainDiffIdxs :: ForTrain [Index]) <- liftO $ flip mapM (map Shape.normalize <$> Ex.train pInputs) $ mapM (flip Map.lookup shape2diffMap)

  let (synthShape2IndexInputShapes, synthShape2IndexReconstruct) = Ex.flatten pInputs
  let synthShape2IndexLabels = concat trainDiffIdxs
  let synthShape2IndexSpec = ESpec (Ex.getInfo synthShape2IndexInputShapes) synthShape2IndexInputShapes synthShape2IndexLabels

  testDiffIdxs :: ForTest [Index] <- Ex.test <$>
    (synthShape2IndexReconstruct <$> (find1 "synthShape2IndexDelta" $ synthShape2Index 4 synthShape2IndexSpec))

  let (nTrainInputs, nOutputs) :: (ForTrain [ShapeC], ForTrain [Maybe ShapeC]) =
        unzip $ flip map (zip (Ex.train pInputs) pOutputs) $ \(inShapes, outShapes) ->
          unzip $ flip map (zip inShapes outShapes) $ \(inShape, outShape) ->
            let (inDiff, outDiff) = shape2shape2idxDiffs inShape outShape in
              (Shape.shiftIndexRev inShape (Shape.upperLeft inShape - inDiff),
                flip fmap outShape $ \outShape -> Shape.shiftIndexRev outShape (Shape.upperLeft outShape - outDiff))

  let nTestInputs :: ForTest [ShapeC] = flip map (zip (Ex.test pInputs) testDiffIdxs) $ \(inShapes, diffIdxs) ->
        flip map (zip inShapes diffIdxs) $ \(inShape, diffIdx) -> Shape.shiftIndex (Shape.normalize inShape) diffIdx

  let nInputs = Ex nTrainInputs nTestInputs

  let reconstruct :: Ex [Maybe ShapeC] -> Ex [Maybe ShapeC]
      reconstruct guesses =
        flip Ex.map (Ex.zip4 pInputs nInputs guesses (Ex trainDiffIdxs testDiffIdxs)) $ \(inShapes, nShapes, nGuesses, diffIdxs) ->
          flip map (List.zip4 inShapes nShapes nGuesses diffIdxs) $ \(inShape, nShape, nGuess, idxDiff) ->
            flip fmap nGuess $ \nGuess -> Shape.shiftIndex nGuess (Shape.upperLeft inShape - idxDiff)

  pure (nInputs, nOutputs, reconstruct)

  where
    -- TODO: confirm that this is sufficient for regressions
    -- TODO: extend this to support int features
    -- TODO: extend this to support distance-from-edge features
    --   - (moderate refactor since it must be computed before flattening)
    synthShape2Index :: Int -> SynthFn CoreM ESpec (Ex ShapeC) Index
    synthShape2Index fuel spec@(ESpec info inputShapes indexLabels) = do
      boolFeatures <- lift . precompute $ do
        shape2bool <- choice "shape2bool" [("2bool", enumBoolFeatures), ("2int2bool", enumIntBoolFeatures)]
        pure $ Ex.map shape2bool inputShapes
      decisionListID [1, 2, 3] synthShape2IndexLeaf $ ESpec info (EagerFeatures boolFeatures, ()) indexLabels

    synthShape2IndexLeaf :: SynthFn CoreM ESpec () Index
    synthShape2IndexLeaf spec = choice "synthShape2IndexLeaf" [
      ("constValueE", constValueE spec)
      ]
