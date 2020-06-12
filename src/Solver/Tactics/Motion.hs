-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE FlexibleContexts #-}
module Solver.Tactics.Motion where

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

data MotionOptions = MotionOptions {
  maxShapesPerExample :: Int,
  minBlanksPerExample :: Int,
  maxESpecs           :: Int,
  maxDisjunctions     :: Int
  } deriving (Eq, Ord, Show)

defaultMotionOptions = MotionOptions {
  maxShapesPerExample = 20,
  minBlanksPerExample = 1,
  maxESpecs           = 10,
  maxDisjunctions     = 10 -- used by a few things, e.g. slide-with-trail ambiguities
  }

-- We try to support the following:
--  - 1e0a9b12 (gravity for all)
--  - 3906de3d (slide one color shapes in one direction, parsing vertical only
--  - 3618c87e (gravity for one color, another color is not solid) *IGNORE*
--  - 56dc2b01 (slide one color towards the other)
--  - d687bc17 (slide everything NOT on the edge to the edge of its color, or drop if n/a)
--  - 05f2a901 (slide one color towards the other)
--  - dc433765 (slide one color 1 step towards the other)
--  - ae3edfdc (slide c1 -> c2 and c3 -> c4)
--  - 8d510a79 (slide with trail where direction depends on color)
--  - d037b0a7 (gravity with trail)
--  - 1caeab9d (align everything with blue)
--  - 5168d44c (move red shape by 2)
--  - d43fd935 (if on ortho with green, slide with trail to green)
--  - 7ddcd7ec (if is isolated, slide AWAY from contact)

type ShapeC = Shape Color

motion :: StdGoal -> SolveM TacticResult
motion goal@(Goal inputs outputs ctx) = find1 "motion" $ do
  guard $ all (uncurry Grid.sameDims) (zip (Ex.train inputs) outputs)
  guard $ all ((>= (minBlanksPerExample defaultMotionOptions)) . Grid.nBlanks) inputs

  allParseOptions <- oneOf "parseOptions" [
    ("reasonable", [
        Parse.Options   { Parse.kind = Parse.ParseLocalAny, Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalNone,  Parse.color = Parse.ParseNoBlanksByColor }
      ]),
    ("unreasonable", [
        Parse.Options { Parse.kind = Parse.ParseLocalH,     Parse.color = Parse.ParseNoBlanksByColor }
        , Parse.Options { Parse.kind = Parse.ParseLocalV,     Parse.color = Parse.ParseNoBlanksByColor }
        ])
    ]

  dOpts <- oneOf "dOpts" $
    concatMap (\fuel -> [("strict:" ++ show fuel, strictOpts fuel), ("relaxed:" ++ show fuel, relaxedOpts fuel)]) [0, 1, 2]
    ++ map (\fuel -> ("strict:" ++ show fuel, strictOpts fuel)) [3, 4]

  allParseMotions <- lift . enumAllG $ do
    ParseResult pInputs pOutputs <- enumParses goal [
      Parse.Options   { Parse.kind = Parse.ParseLocalAny, Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalOrtho, Parse.color = Parse.ParseNoBlanksByColor }
      , Parse.Options { Parse.kind = Parse.ParseLocalNone,  Parse.color = Parse.ParseNoBlanksByColor }
      ]

    guard $ all ((<= (maxShapesPerExample defaultMotionOptions)) . length) pInputs
    let candidateMotions :: ForTrain [[Maybe (Shape Color)]] = map (List.uncurry3 Motion.alignShapes2ShapesD) (zip3 (Ex.train inputs) (Ex.train pInputs) pOutputs)
    let actx :: ArcContext = ArcContext (EagerFeatures (ctxInts ctx)) (EagerFeatures (ctxColors ctx))
    let dspec = DSpec (Ex.getInfo inputs) (pInputs, inputs, actx) candidateMotions
    espec <- DSpec.blast dspec
    guard $ DSpec.nExactSpecs dspec < maxESpecs defaultMotionOptions
    guard $ any (any (not . Maybe.isNothing)) (ESpec.labels espec)
    guard $ flip any (zip (Ex.train pInputs) (ESpec.labels espec)) $ \(inShapes, labels) ->
      flip any (zip inShapes labels) $ \(inShape, label) ->
        case label of
          Nothing -> False
          Just outShape -> inShape /= outShape
    pure $ (pInputs, espec)

  (pInputs, espec) <- oneOf "parseMotion" $ sortUniqueParseMotions goal allParseMotions
  guesses          <- find1 "synthMoveShapes2Shapes" $ synthMoveShapes2Shapes dOpts espec

  let newInputs = flip Ex.map (Ex.zip3 pInputs inputs guesses) $ \(inShapes, input, outShapes) ->
        let (replaceIns, replaceOuts) = unzip $ filter (Maybe.isJust . snd) (zip inShapes outShapes) in
          Grid.replacingShapes input replaceIns (map Maybe.fromJust replaceOuts)

  pure $ TacticResult.Decompose (Goal newInputs outputs ctx) pure

    where
      sortUniqueParseMotions goal parses =
        let uniqSorted = List.stableUniqKey Guess.value $ List.sortOn (score goal) parses in
          map (\guess -> (History.showCondensed (Guess.history guess), Guess.value guess)) uniqSorted

      score (Goal _ outputs _) (Guess (_, ESpec _ _ labels) _ _ _) = (nOutputPointsUnexplained outputs labels, sum (map length labels))

      nOutputPointsUnexplained outputs labels = sum . flip map (zip outputs labels) $ \(output, labels) ->
        Grid.nNonBlankVals output - sum (map (\s -> case s of Nothing -> 0; Just s -> Shape.nPoints s) labels)


synthMoveShapes2Shapes :: DListOptions -> SynthFn CoreM ESpec (Ex [Shape Color], Ex (Grid Color), ArcContext) [Maybe (Shape Color)]
synthMoveShapes2Shapes dOpts spec@(ESpec info (inShapes, inputs, actx) outShapes) = do
  boolFeaturesSeq :: [Choice (Ex [Bool])] <- lift . precompute $ do
    neg <- choice "negate" [("no", pure id), ("yes", pure not)]
    gridsShape2Bool <- choice "boolFeatures" [
      -- TODO: more crazy features? ranking concerns?
      ("all", pure $ \g s -> True),
      ("hasValues", do
        c <- enumVals -- TODO: easy to have context here
        pure $ \g s -> Set.member c (Shape.values s)),
      ("isSingleton", pure $ \g s -> Shape.nPoints s == 1)
      ]
    let phi g s = neg (gridsShape2Bool g s)
    pure $ Ex.map (\(g, inShapes) -> map (neg . gridsShape2Bool g) inShapes) (Ex.zip inputs inShapes)

  intFeaturesSeq :: [Choice (Ex [Int])] <- lift . precompute $ choice "intFeaturesSeq" [
    ("indep", do
        shape2int <- enumIntFeatures
        pure $ Ex.map (map shape2int) inShapes),
    ("diffs", do
        -- Inspired by 1caeab9d
        -- Alt: make arithmetic do the arithmetic, and have a single Int for each example (that gets replicated)
        shape2int <- enumIntFeatures
        bs <- oneOf "boolFeaturesSeq" boolFeaturesSeq
        flip Ex.mapM (Ex.zip inShapes bs) $ \(inShapes, bs) -> do
          guard $ length (filter id bs) == 1
          let special = shape2int . fst . head . filter snd $ zip inShapes bs
          pure $ map (\s -> shape2int s - special) inShapes)]

  -- TODO: maybe features here or not? This is related to the notorious "Option Color" debate
  axDirFeaturesSeq :: [Choice (Ex [Maybe (Axis, Direction)])] <- lift . precompute $ do
    rev  <- oneOf "reverseDirection" [("keep", id), ("reverse", Direction.reverse)]
    bs   <- oneOf "boolFeaturesForAxDirFeatures" boolFeaturesSeq
    maybeAxDirs <- findSpecialAxDirFeature inputs inShapes bs
    pure $ flip Ex.map maybeAxDirs $ \maybeAxDirs -> map (fmap (\(ax, dir) -> (ax, rev dir))) maybeAxDirs

  let boolFeatures  :: [Choice (Ex Bool)] = List.stableUniqKey (Ex.train . snd) $ flip map boolFeaturesSeq $ \(name, bs) -> (name, fst $ Ex.flatten bs)
  let intFeatures   :: [Choice (Ex Int)]  = List.stableUniqKey (Ex.train . snd) $ flip map intFeaturesSeq  $ \(name, ns) -> (name, fst $ Ex.flatten ns)

  let axDirFeatures :: [Choice (Ex (Maybe (Axis, Direction)))] = flip map axDirFeaturesSeq $ \(name, axDirs) -> (name, fst $ Ex.flatten axDirs)
  let allAxDirFeatures :: [Choice (Ex (Maybe (Axis, Direction)))] = List.stableUniqKey snd axDirFeatures
  let allBoolFeatures :: [Choice (Ex Bool)] = List.stableUniqKey snd (boolFeatures ++ map (\(name, exs) -> (name, Ex.map Maybe.isJust exs)) allAxDirFeatures)

  let (inShapesFlat   :: Ex (Shape Color), reconstructFlattened) = Ex.flatten inShapes
  let inputsFlat = Ex.replicateLikeNested inShapes inputs
  let labelsFlat      :: ForTrain (Maybe (Shape Color)) = concat outShapes
  let ctxFlat = (EagerFeatures allBoolFeatures, (inShapesFlat, (inputsFlat, (EagerFeatures allAxDirFeatures, EagerFeatures intFeatures))))

  reconstructFlattened <$> decisionList dOpts synthMoveShape2MaybeShape (ESpec (Ex.getInfo inShapesFlat) ctxFlat labelsFlat)

findSpecialAxDirFeature :: Ex (Grid Color) -> Ex [Shape Color] -> Ex [Bool] -> SolveM (Ex [Maybe (Axis, Direction)])
findSpecialAxDirFeature inputs inShapes specials = do
  axes <- enumVals
  flip Ex.mapM (Ex.zip3 inputs inShapes specials) $ \(input, inShapes, specials) -> do
    let allAxDirsFromTo :: [[(Axis, Direction)]] = flip map inShapes $ \inShape ->
          flip concatMap (zip inShapes specials) $ \(outShape, special) ->
            if outShape == inShape then [] else
              if not special then [] else
                Shape.axDirsFromTo inShape outShape axes
    guard $ all ((<2) . length) allAxDirsFromTo
    pure $ map List.headO allAxDirsFromTo

synthMoveShape2MaybeShape :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), (EagerFeatures (Maybe (Axis, Direction)), EagerFeatures Int))) (Maybe (Shape Color))
synthMoveShape2MaybeShape spec@(ESpec info (inShapes, (inputs, (axDirs, ints))) outShapes) = do
  choice "synthMoveShape2MaybeShape" [
    ("allNothing", do
        guard $ all Maybe.isNothing outShapes
        constValueE spec),
    ("allJust", do
        guard $ all Maybe.isJust outShapes
        guesses <- synthMoveShape2Shape $ ESpec info (inShapes, (inputs, (axDirs, ints))) (map Maybe.fromJust outShapes)
        pure $ Ex.map Just guesses)
    ]

synthMoveShape2Shape :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), (EagerFeatures (Maybe (Axis, Direction)), EagerFeatures Int))) (Shape Color)
synthMoveShape2Shape spec@(ESpec info (inShapes, (inputs, (axDirs, ints))) outShapes) = choice "synthMoveShape2Shape" [
  ("identityP",   identityP $ ESpec info inShapes outShapes),
  ("slideUntil",  do
      outAxDirs :: ForTrain (Axis, Direction) <- liftL . take (maxDisjunctions defaultMotionOptions) $ flip mapM (zip3 (Ex.train inputs) (Ex.train inShapes) outShapes) $ \(input, inShape, outShape) ->
        Motion.slideReaches input inShape outShape
      guesses   <- synthShape2AxDir $ ESpec info (inShapes, (inputs, axDirs)) outAxDirs
      pure $ flip Ex.map (Ex.zip3 inputs inShapes guesses) $ \(input, inShape, (ax, dir)) ->
        Motion.apply (Motion ax dir Nothing NoTrail) input inShape),
  ("slideSteps",  do
      outAxDirSteps :: ForTrain (Axis, Direction, Int) <- liftL . take (maxDisjunctions defaultMotionOptions) $ flip mapM (zip3 (Ex.train inputs) (Ex.train inShapes) outShapes) $ \(input, inShape, outShape) ->
        Motion.slideSteps input inShape outShape
      (guessAxDirs, guessSteps) <- choice "slideSteps" [
        ("axDir-steps", do
            guessAxDirs <- synthShape2AxDir $ ESpec info (inShapes, (inputs, axDirs)) $ map (\(ax, dir, _) -> (ax, dir)) outAxDirSteps
            guessSteps  <- synthShape2Steps $ ESpec info (inShapes, (inputs, (axDirs, ints))) $ map (\(_, _, k) -> k) outAxDirSteps
            pure (guessAxDirs, guessSteps)),
        ("ax-steps", do
            let outAxSteps :: ForTrain (Axis, Int) = flip map outAxDirSteps $ \(ax, dir, k) ->
                  case dir of
                    Normal -> (ax, k)
                    Reverse -> (ax, -k)
            guessAxs    <- synthShape2Ax $ ESpec info (inShapes, (inputs, axDirs)) $ map (\(ax, _) -> ax) outAxSteps
            guessSteps  <- synthShape2Steps $ ESpec info (inShapes, (inputs, (axDirs, ints))) $ map (\(_, k) -> k) outAxSteps
            -- TODO: this is silly, but Motion.apply cannot handle negative step sizes!!
            pure $ Ex.unzip $ flip Ex.map (Ex.zip guessAxs guessSteps) $ \(ax, k) ->
                  if k < 0 then ((ax, Reverse), -k) else ((ax, Normal), k))
        ]
      pure $ flip Ex.map (Ex.zip4 inputs inShapes guessAxDirs guessSteps) $ \(input, inShape, (ax, dir), nSteps) ->
        Motion.apply (Motion ax dir (Just nSteps) NoTrail) input inShape),
  ("slideWithTrail",  do
      outAxDirDelta :: ForTrain (Axis, Direction, Int) <- liftL . take (maxDisjunctions defaultMotionOptions) $ flip mapM (zip3 (Ex.train inputs) (Ex.train inShapes) outShapes) $ \(input, inShape, outShape) ->
        Motion.slideTrailReaches input inShape outShape
      guessAxDirs <- synthShape2AxDir $ ESpec info (inShapes, (inputs, axDirs)) $ map (\(ax, dir, _) -> (ax, dir)) outAxDirDelta
      guessDeltas  <- synthShape2Delta $ ESpec info (inShapes, (inputs, guessAxDirs)) $ map (\(_, _, d) -> d) outAxDirDelta
      let guesses =  flip Ex.map (Ex.zip4 inputs inShapes guessAxDirs guessDeltas) $ \(input, inShape, (ax, dir), delta) ->
            Motion.apply (Motion ax dir Nothing (WithTrail delta)) input inShape
      pure guesses)
  ]

synthShape2AxDir :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), EagerFeatures (Maybe (Axis, Direction)))) (Axis, Direction)
synthShape2AxDir spec@(ESpec info (inShapes, (inputs, axDirFeatures)) outAxDirs) = choice "synthShape2AxDir" [
  ("constValueE", constValueE spec),
  ("identityP", do
      axDirMaybe <- oneOf "axDirFeature" (EagerFeatures.choices axDirFeatures)
      axDir <- liftO $ Ex.mapM id axDirMaybe
      identityP (ESpec info axDir outAxDirs))
  ]

synthShape2Ax :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), EagerFeatures (Maybe (Axis, Direction)))) Axis
synthShape2Ax spec@(ESpec info (inShapes, (inputs, axDirFeatures)) outAxs) = choice "synthShape2Ax" [
  ("constValueE", constValueE spec),
  ("identityP", do
      axDirMaybe <- oneOf "axDirFeature" (EagerFeatures.choices axDirFeatures)
      axDir <- liftO $ Ex.mapM id axDirMaybe
      identityP (ESpec info (Ex.map fst axDir) outAxs))
  ]

synthShape2Steps :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), (EagerFeatures (Maybe (Axis, Direction)), EagerFeatures Int))) Int
synthShape2Steps spec@(ESpec info (inShapes, (inputs, (axDirFeatures, ints))) outSteps) = choice "synthShape2Steps" [
  ("arith", synthInts2IntE $ ESpec info ints outSteps)
  ]

synthShape2Delta :: SynthFn CoreM ESpec (Ex (Shape Color), (Ex (Grid Color), Ex (Axis, Direction))) Int
synthShape2Delta spec@(ESpec info (inShapes, (inputs, axDirs)) outDeltas) = choice "synthShape2AxDelta" [
  ("constValueE", constValueE spec),
  ("identityP", do
      let deltas = flip Ex.map (Ex.zip inShapes axDirs) $ \(s, (ax, dir)) -> Shape.minimalNonSelfIntersectingDelta s ax dir
      identityP $ ESpec info deltas outDeltas)
  ]
