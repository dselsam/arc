-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Shape where

import Debug.Trace
import Util.Imports
import Lib.Axis
import Lib.Blank
import qualified Lib.Index as Index
import qualified Util.Map as Map
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import qualified Util.List as List
import Synth.Ex (Ex(Ex))
import qualified Synth.Ex as Ex
import Synth1.Basic
import Util.List (range)
import Search.SearchT
import Synth.LazyFeatures
import Lib.Index (Index(..))
import Lib.Dims (Dims(..))
import qualified Data.List as List
import qualified Lib.Dims as Dims
import qualified Data.Map as Map
import Lib.Axis (Axis(..))
import qualified Lib.Axis as Axis
import Lib.Direction (Direction(..))
import qualified Lib.Direction as Direction
import Lib.Rect (Rect(..))
import qualified Lib.Rect as Rect
import qualified Synth.EagerFeatures as EagerFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Synth.EagerFeatures
import Synth.LazyFeatures

data Shape a = Shape {
  idx2val :: Map Index a
  } deriving (Eq, Ord)

instance (Show a) => Show (Shape a) where
  show (Shape map) = Map.iter map "SHAPE: " $ \s idx val -> s ++ " " ++ show (idx, val)

-- Makers

empty :: Shape a
empty = Shape { idx2val = Map.empty }

singleton :: Index -> a -> Shape a
singleton idx x = Shape { idx2val = Map.insert idx x Map.empty }

union :: Shape a -> Shape a -> Shape a
union s1 s2 = Shape { idx2val = Map.union (idx2val s1) (idx2val s2) }

insert :: Index -> a -> Shape a -> Shape a
insert idx x s = Shape { idx2val = Map.insert idx x (idx2val s) }

filter :: (Eq a, Ord a) => (Index -> Bool) -> Shape a -> Shape a
filter p s = Shape { idx2val = Map.filterWithKey (\idx _ -> p idx) (idx2val s) }

intersect :: Shape a -> Shape a -> Shape a
intersect s1 s2 = Shape { idx2val = Map.intersection (idx2val s1) (idx2val s2) }

difference :: Shape a -> Shape a -> Shape a
difference s1 s2 = Shape { idx2val = Map.difference (idx2val s1) (idx2val s2) }

fromList :: [(Index, a)] -> Shape a
fromList xs = Shape (Map.fromList xs)

-- Helpers

null :: Shape a -> Bool
null s = Map.null (idx2val s)

getOpt :: Shape a -> Index -> Maybe a
getOpt s idx = Map.lookup idx (idx2val s)

lookup :: Shape a -> Index -> Maybe a
lookup s idx = Map.lookup idx (idx2val s)

firstVal :: Shape a -> Maybe a
firstVal s = do
  guard . not . Map.null . idx2val $ s
  pure . snd . Map.elemAt 0 . idx2val $ s

containsIndex :: Shape a -> Index -> Bool
containsIndex s idx = Map.member idx (idx2val s)

containsVal :: (Eq a) => a -> Shape a -> Bool
containsVal x s = x `elem` (Map.elems (idx2val s))

lookupIndex :: Shape a -> Index -> Maybe a
lookupIndex s idx = Map.lookup idx (idx2val s)

subsetMatches :: (Eq a) => Shape a -> Shape a -> Bool
subsetMatches s1 s2 = flip all (Map.assocs (idx2val s1)) $ \(idx, v1) ->
  case Map.lookup idx (idx2val s2) of
    Nothing -> False
    Just v2 -> v1 == v2

intersects :: Shape a -> Shape a -> Bool
intersects s1 s2 = not . Map.null . idx2val $ intersect s1 s2

indices :: Shape a -> [Index]
indices s = Map.keys $ idx2val s

assocs :: Shape a -> [(Index, a)]
assocs s = Map.assocs $ idx2val s

sameIndices :: Shape a -> Shape a -> Bool
sameIndices s1 s2 = indices s1 == indices s2

minDist :: DistType -> Shape a -> Shape b -> Maybe Int
minDist distType s1 s2 = do
  guard . not . Lib.Shape.null $ s1
  guard . not . Lib.Shape.null $ s2
  pure $ minimum $ do
    x1 <- Map.keys (idx2val s1)
    x2 <- Map.keys (idx2val s2)
    pure $ Axis.dist distType x1 x2

minDistToIdx :: DistType -> Index -> Shape a -> Maybe Int
minDistToIdx distType idx s = do
  guard . not . Lib.Shape.null $ s
  pure $ minimum $ do
    x <- Map.keys (idx2val s)
    pure $ Axis.dist distType x idx

-- Int features

nPoints :: Shape a -> Int
nPoints = Map.size . idx2val

nDistinctVals :: (Ord a) => Shape a -> Int
nDistinctVals = List.countDistinct id . Map.elems . idx2val

-- Color features
uniformColorOpt :: (Eq a, Ord a) => Shape a -> Maybe a
uniformColorOpt s = List.getUnique id . Map.elems . idx2val $ s

nOrthoEdges :: Dims -> Shape a -> Int
nOrthoEdges dims s = length $ flip List.filter (Dims.edgePredicates dims) $ flip any (indices s)

-- Bool features

isBounded :: Dims -> Shape a -> Bool
isBounded dims s = nOrthoEdges dims s == 0

isSemiBounded :: Dims -> Shape a -> Bool
isSemiBounded dims s = nOrthoEdges dims s `elem` [1, 2]

isUnbounded :: Dims -> Shape a -> Bool
isUnbounded dims s = nOrthoEdges dims s > 2

isRect :: Shape a -> Bool
isRect s = flip all (Rect.getPerimeterIdxs sRect) (\idx -> containsIndex s idx)
  where
    sRect = enclosingRect s

-- allows non-filled rects to be identified if they go off the edge. Motivated by ec88
isRectOffEdge :: Dims -> Shape a -> Bool
isRectOffEdge ds s = flip all (Rect.getPerimeterIdxs sRect) (\idx ->
                       containsIndex s idx || Dims.onEdge ds idx)
  where
    sRect = enclosingRect s

isFilledRect :: Shape a -> Bool
isFilledRect s = Rect.area (enclosingRect s) == nPoints s

containsFrame :: Shape a -> Bool
containsFrame s = all (containsIndex s) (Rect.getPerimeterIdxs $ enclosingRect s)

isUniform :: (Eq a) => Shape a -> Bool
isUniform s = List.allSame . Map.elems . idx2val $ s

fromRect :: Rect -> a -> Shape a
fromRect r x = Shape $ Map.fromList (zip (Rect.getIdxs r) (replicate (Rect.area r) x))

isOrthoLine :: Shape a -> Bool
isOrthoLine s = isFilledRect s && (Rect.nRows (enclosingRect s) == 1 || Rect.nCols (enclosingRect s) == 1)

getBoundedLazyFeatures :: (Monad m) => Ex Dims -> Ex [Shape a] -> LazyFeatures m [Bool]
getBoundedLazyFeatures dims shapes = LazyFeatures $ choice "Shapes.getBoundedLazyFeatures.Bools" [
    ("isBounded",     pure $ Ex.map (\(dims, shapes) -> Prelude.map (isBounded dims)     shapes) $ Ex.zip dims shapes),
    ("isSemiBounded", pure $ Ex.map (\(dims, shapes) -> Prelude.map (isSemiBounded dims) shapes) $ Ex.zip dims shapes),
    ("isUnbounded",   pure $ Ex.map (\(dims, shapes) -> Prelude.map (isUnbounded dims)   shapes) $ Ex.zip dims shapes)
    ]

-- Set-valued features

values :: (Ord a) => Shape a -> Set a
values = Set.fromList . Map.elems . idx2val

enumSetFeatures :: (Monad m, Ord a) => SearchT m (Shape a -> Set a)
enumSetFeatures = pure values

valuesToList :: (Ord a) => Shape a -> [a]
valuesToList = Map.elems . idx2val

-- Transformations

map :: (a -> b) -> Shape a -> Shape b
map f s = s { idx2val = Map.map f (idx2val s) }

-- TODO: store this in the shape?
enclosingRect :: Shape a -> Rect
enclosingRect s
  | nPoints s == 0 = Rect.empty
  | otherwise      =
    -- TODO: handle the edge cases
    let (minRow, maxRow, minCol, maxCol) = Map.iter (idx2val s) (10000, 0, 10000, 0) $ \(minRow, maxRow, minCol, maxCol) (Index i j) _ ->
          (min minRow i, max maxRow i, min minCol j, max maxCol j)
    in
      Rect { Rect.upperLeft = Index minRow minCol, Rect.dims = Dims (maxRow + 1 - minRow) (maxCol + 1 - minCol) }

move :: Shape a -> Int -> Axis -> Direction -> Shape a
move s k ax dir = Shape $ Map.iter (idx2val s) Map.empty $ \acc idx x ->
  let newIdx = idx + (Index.scale (k * Direction.toScale dir) (Axis.toDelta ax)) in
    Map.insert newIdx x acc

fill :: b -> Shape a -> Shape b
fill y s = Shape { idx2val = fmap (\_ -> y) (idx2val s) }

shiftIndex :: Shape a -> Index -> Shape a
shiftIndex s ul = Shape $ Map.mapKeys (\idx -> idx + ul) (idx2val s)

shiftIndexRev :: Shape a -> Index -> Shape a
shiftIndexRev s ul = Shape $ Map.mapKeys (\idx -> idx - ul) (idx2val s)

normalize :: Shape a -> Shape a
normalize s =
  let Rect (Index dx dy) _ = enclosingRect s in
    shiftIndex s (Index (- dx) (- dy))

discardValues :: Shape a -> Shape ()
discardValues = Lib.Shape.map (\_ -> ())

upperLeft :: Shape a -> Index
upperLeft = Rect.upperLeft . enclosingRect

fillRectWith :: a -> Rect -> Shape a -> Shape a
fillRectWith x rect s = List.iter (Rect.getIdxs rect) s $ \acc idx -> pure $
  if containsIndex acc idx then acc else insert idx x acc

-- This is perf-relevant
-- TODO: maybe, in case it is not an enclosing rectangle
frameRectWith :: (Show a) => a -> Shape a -> Shape a
frameRectWith x s = List.iter (Rect.getPerimeterIdxs . Rect.addFrame . enclosingRect $ s) s $ \acc idx -> pure $
  insert idx x acc

-- TODO(jesse, May 20 2020, 10:51 AM): implement when there is time
-- frameRectWithOneSided :: (Show a) => a -> Shape a -> Axis -> Direction -> Shape a
-- frameRectWithOneSided x s axis direction = _

replaceFrameWith :: (Show a) => a -> Shape a -> Shape a
replaceFrameWith x s = List.iter (Rect.getPerimeterIdxs . enclosingRect $ s) s $ \acc idx -> pure $
  insert idx x acc

hasNonBlank :: (HasBlank a) => Shape a -> Bool
hasNonBlank s = any nonBlank $ Map.elems (idx2val s)

unifyShapesOnRects :: (Eq a, Ord a, Show a) => [Shape a] -> [Rect] -> Maybe (Shape a)
unifyShapesOnRects shapes rects = do
  -- first make sure they are consistent
  sUnion :: Shape a <- Shape <$> Map.glueMaps (Prelude.map idx2val shapes)
  -- next, make sure they are consistent with *negative* space on the provided rects
  guard $ flip all (zip shapes rects) $ \(s, r) ->
    flip all (indices sUnion) $ \idx ->
      (Rect.containsIndex r idx) <= containsIndex s idx
  pure $ sUnion

minimalNonSelfIntersectingDelta :: Shape a -> Axis -> Direction -> Int
minimalNonSelfIntersectingDelta s ax dir = core 1
  where
    core i = if intersects (move s i ax dir) s then core (i+1) else i

axDirsFromTo :: (HasBlank a) => Shape a -> Shape a -> [Axis] -> [(Axis, Direction)]
axDirsFromTo inShape outShape axes = do
  ax  <- axes
  dir <- [Normal, Reverse]
  guard $ flip any (indices inShape) $ \idx1 ->
    flip any (indices outShape) $ \idx2 ->
      Axis.onSame ax idx1 idx2 && Direction.precedes ax dir idx1 idx2
  pure (ax, dir)

-- Advanced

-- TODO: are we sure we want to return Just in the already-a-rect case?
maxSubRect :: (Show a, Eq a, Ord a) => Shape a -> Maybe Rect
maxSubRect s
  | isFilledRect s = Just (enclosingRect s)
  | otherwise      =
    let r = core s (enclosingRect s) in
      r

  where
    core :: Shape a -> Rect -> Maybe Rect
    core s r@(Rect (Index i j) (Dims dx dy)) = do
      let candidates = [
            (Vertical,   Reverse, sum . flip Prelude.map (range dy) $ \k -> b2i $ containsIndex s (Index i        (j+k))),
            (Vertical,   Normal,  sum . flip Prelude.map (range dy) $ \k -> b2i $ containsIndex s (Index (i+dx-1) (j+k))),
            (Horizontal, Reverse, sum . flip Prelude.map (range dx) $ \k -> b2i $ containsIndex s (Index (i+k)     j)),
            (Horizontal, Normal,  sum . flip Prelude.map (range dx) $ \k -> b2i $ containsIndex s (Index (i+k)    (j+dy-1)))
            ]
      let (_, _, mostMissing) = List.maximumBy (comparing (\(_, _, k) -> k)) candidates
      if mostMissing == 0
        then Just r
        else case List.argmaxesKey (\(_, _, k) -> k) candidates of
               [(ax, dir, _)] -> core s (Rect.rmSide r ax dir)
               _              -> Nothing

    b2i :: Bool -> Int
    b2i False = 1 -- Note the negation
    b2i True  = 0

cropToMajorityVal :: (Eq a) => Shape a -> Shape a
cropToMajorityVal s = Shape . Map.fromList $
  let counts = List.counts $ Map.elems (idx2val s)
      maxCount = List.maximum counts in
    List.map fst $ flip List.filter (zip (Map.assocs (idx2val s)) counts) $ \((idx, val), count) -> count == maxCount

isResultOfFillRect :: (Ord a) => Shape a -> Shape a -> Maybe a
isResultOfFillRect inShape outShape = do
  guard $ subsetMatches inShape outShape
  let newColors = Map.elems . idx2val $ difference outShape inShape
  guard $ List.countDistinct id newColors == 1
  let newColor = head newColors
  -- motivated by 84f
  let pretendShape = union outShape (fill newColor inShape)
  guard $ isFilledRect pretendShape
  pure $ newColor

  {-
containsPerimeter :: Shape a -> Bool
containsPerimeter s =
-}

hasUniformFrame :: (Ord a) => Shape a -> Maybe a
hasUniformFrame s = do
  let maybeValues = Prelude.map (Lib.Shape.lookup s) (Rect.getPerimeterIdxs . enclosingRect $ s)
  guard . not . List.null $ maybeValues
  guard $ all Maybe.isJust maybeValues
  guard $ List.countDistinct id maybeValues == 1
  pure . Maybe.fromJust . head $ maybeValues

isResultOfFrameRect :: (Ord a) => Shape a -> Shape a -> Maybe a
isResultOfFrameRect inShape outShape = do
  guard $ subsetMatches inShape outShape
  guard $ enclosingRect outShape == Rect.addFrame (enclosingRect inShape)
  hasUniformFrame outShape

-- no shapes in inShapes can be null!
uniqueNearestShape :: (Eq a) => DistType -> [Shape a] -> [Maybe (Shape a)]
uniqueNearestShape distType inShapes =
  flip Prelude.map closestShapes $ \closestList -> if length closestList == 1 then Just (closestList !! 0) else Nothing
  where
    -- note we rely on Ord (Maybe Int). Is safe as long as no null shapes are passed
    closestShapes = flip Prelude.map inShapes $ \s -> List.argminsKey (\s2 -> minDist distType s s2) (List.filter (\s2 -> s2 /= s) inShapes)

-- the cool distance from 6df30ad6
uniqueNearestShapeSpecial :: (Eq a, Show a) => [Shape a] -> [Maybe (Shape a)]
uniqueNearestShapeSpecial inShapes = flip Prelude.map inShapes $ \inShape ->
  let closestOrthos = List.map (\s -> (minDist OrthoDist inShape s, s)) . List.filter (/= inShape) $ inShapes
      bestOrthos    = safeArgminsKey fst closestOrthos
      closestDiags  = List.map (\s -> (minDist DiagDist inShape s, s)) . List.filter (/= inShape) $ inShapes
      bestDiags     = safeArgminsKey fst closestDiags
      best          = safeArgminsKey fst (bestOrthos ++ bestDiags)
  in
    fmap snd $
      if List.null best then Nothing
      else if length best == 1 then Just (head best)
      else if fst (head bestOrthos) <= fst (head bestDiags)  && length bestOrthos == 1 then Just (head bestOrthos)
      else if fst (head bestDiags)  <  fst (head bestOrthos) && length bestDiags == 1  then Just (head bestDiags)
      else Nothing

  where
    safeArgminsKey key xs = if List.null xs then [] else List.argminsKey key xs

-- TODO (perf): can short-circuit with first. match first idx from pTouch to be within 0 or 1 of s
-- first to have a diagDist of 1!
-- Spec: returns the subset of all shapes that touch the shape
shapesTouchingShape :: Shape a -> [Shape a] -> [Shape a]
shapesTouchingShape s potentialTouchers =
  flip Prelude.filter potentialTouchers $ \pTouch ->
    case minDist DiagDist s pTouch of
      Nothing -> False
      Just distBtwShapes -> distBtwShapes == 1


-- if a shape is only touching one other shape, returns Just <that shape touching it>
uniqueTouchingShape :: (Eq a) => [Shape a] -> [Maybe (Shape a)]
uniqueTouchingShape inShapes =
  flip Prelude.map touchingShapes $ \touchingList -> if length touchingList == 1 then Just (touchingList !! 0) else Nothing
  where
    touchingShapes = flip Prelude.map inShapes $ \s -> shapesTouchingShape s (List.filter (\s2 -> s2 /= s) inShapes)


-- note that it is defined by the enclosing rectangles
shapeContainerAux :: (Eq a) => [Shape a] -> [(Maybe (Shape a), Maybe (Shape a))]
shapeContainerAux inShapes =
  flip Prelude.map shapeContainers $ \containerList ->
    if List.null containerList then (Nothing, Nothing)
    else (Just (minShapeByRectArea containerList), Just (maxShapeByRectArea containerList))
  where
    shapeContainers = flip Prelude.map inShapes $ \s -> flip List.filter inShapes $
      \s2 -> s2 /= s && Rect.contains2nd (enclosingRect s2) (enclosingRect s)

    maxShapeByRectArea = \shapes -> (List.argmaxKey (\shape -> Rect.area (enclosingRect shape)) shapes)
    minShapeByRectArea = \shapes -> (List.argminKey (\shape -> Rect.area (enclosingRect shape)) shapes)

minShapeContainer :: (Eq a) => [Shape a] -> [Maybe (Shape a)]
minShapeContainer inShapes = List.map fst $ shapeContainerAux inShapes

maxShapeContainer :: (Eq a) => [Shape a] -> [Maybe (Shape a)]
maxShapeContainer inShapes = List.map snd $ shapeContainerAux inShapes

majorityVal :: (Eq a, Ord a) => Shape a -> a
majorityVal = List.mostCommon  . valuesToList

minorityVal :: (Eq a, Ord a) => Shape a -> a
minorityVal = List.leastCommon . valuesToList

-- Motivated by 2a5f
uniqueSameNormalizedIndices :: (Eq a) => [Shape a] -> [Maybe (Shape a)]
uniqueSameNormalizedIndices inShapes = flip List.map inShapes $ \inShape -> do
  let matchingShapes = List.filter (\s -> s /= inShape && sameIndices (normalize s) (normalize inShape)) inShapes
  guard $ length matchingShapes == 1
  pure $ head matchingShapes

isTouchingShapeUniformVal :: (Eq a, Ord a) => a -> [Shape a] -> [Bool]
isTouchingShapeUniformVal x shapes = flip List.map shapes $ \s1 -> not . List.null $
  flip List.filter (shapesTouchingShape s1 shapes) $ \s2 -> uniformColorOpt s2 == Just x


-- biggegst thing each sape contains
-- smallest thing eachshape contains

-- the smallest thing contained in each shape
-- Nothing if shape doesn't contain anything, or if it doesn't have a unique smallest hting contained
-- Note ew compute containment via enclosing rectangle, but size by Shape.nPoints
smallestInShape :: (Eq a, Ord a) => [Shape a] -> [Maybe (Shape a)]
smallestInShape inShapes =
  flip List.map inShapes $ \inShape ->
    -- the thing that inShape contains
    let containedShapes = List.filter (\s -> Rect.contains2nd (enclosingRect inShape) (enclosingRect s)) inShapes
        minContainedShapes = if List.null containedShapes then [] else List.argminsKey (\s -> nPoints s) containedShapes in
      if (length minContainedShapes) == 1 then Just (minContainedShapes !! 0) else Nothing

biggestInShape :: (Eq a, Ord a) => [Shape a] -> [Maybe (Shape a)]
biggestInShape inShapes =
  flip List.map inShapes $ \inShape ->
    let containedShapes = List.filter (\s -> Rect.contains2nd (enclosingRect inShape) (enclosingRect s)) inShapes
        maxContainedShapes = if List.null containedShapes then [] else List.argmaxesKey (\s -> nPoints s) containedShapes in
      if (length maxContainedShapes) == 1 then Just (maxContainedShapes !! 0) else Nothing
