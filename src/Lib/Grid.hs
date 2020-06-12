-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}

module Lib.Grid where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import qualified Data.Maybe as Maybe
import Data.Foldable
import qualified Data.List as List
import Data.Map (Map)
import Data.Hashable
import Data.Vector.Instances
import qualified Data.Map as Map
import Data.Maybe (listToMaybe, isJust)
import Data.Monoid
import Data.Monoid (mempty)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as BVector
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving
import Debug.Trace

import Lib.Axis
import qualified Lib.Axis as Axis
import Lib.Direction (Direction(..))
import qualified Lib.Direction as Direction
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import Lib.Color (Color, enumColorsCtx)
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import Synth1.Synth1Context
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import qualified Lib.Line as Line

import Util.Imports
import qualified Util.Int as Int
import Util.List (uncurry3, range)
import qualified Util.Int as Int
import qualified Util.List as List
import Lib.Shape (Shape)
import qualified Lib.Shape as Shape
import Lib.Rect (Rect(Rect))
import qualified Lib.Rect as Rect
import qualified Lib.BGrid as Box

import Search.SearchT

import Synth1.Basic
import Synth.Ex (Ex(..))
import qualified Synth.Ex as Ex

data Grid a = Grid {
  dims        :: Dims,
  gridData    :: !(Vector a)
  } deriving (Eq, Ord, Generic, Generic1)

instance NFData a => NFData (Grid a)

instance (Unbox a, Hashable a) => Hashable (Grid a) where
  hashWithSalt salt g = hashWithSalt salt (dims g, gridData g)

nRows g  = Dims.nRows . dims $ g
nCols g  = Dims.nCols . dims $ g
nCells g = nRows g * nCols g

fromArray :: (Unbox a) => Dims -> Vector a -> Grid a
fromArray dims v | Dims.nCells dims == Vector.length v = Grid dims v

fromList :: (Unbox a) => Dims -> [a] -> Grid a
fromList dims elems = fromArray dims (Vector.fromList elems)

fromLists :: (Unbox a) => [[a]] -> Grid a
fromLists [] = Grid (Dims 0 0) (Vector.fromList [])
fromLists elems =
  let m = length elems
      n = length (head elems) in
    fromArray (Dims m n) (Vector.fromList $ concat elems)

fromBox :: (Unbox a) => Box.Grid a -> Grid a
fromBox box = Grid (Box.dims box) (Vector.fromList $ Box.toList box)

fromIntLists :: [[Int]] -> Grid Int
fromIntLists elems = fromLists elems

-- TODO: duplication
fromFuncM :: (Unbox a, Monad m) => Dims -> (Index -> m a) -> m (Grid a)
fromFuncM dims@(Dims m n) f = do
  elems <- Vector.generateM (m*n) $ \i -> f (Dims.int2index dims i)
  pure $ fromArray dims elems

fromFunc :: (Unbox a) => Dims -> (Index -> a) -> Grid a
fromFunc dims@(Dims m n) f = fromArray dims $ Vector.generate (m*n) $ \i -> f (Dims.int2index dims i)

const :: (Unbox a) => Dims -> a -> Grid a
const dims@(Dims m n) x = fromArray dims $ Vector.replicate (m*n) x

allBlank :: (Unbox a, HasBlank a) => Grid a -> Bool
allBlank g = Dims.all (dims g) $ \idx -> isBlank (getG g idx)

nBlanks :: (Unbox a, HasBlank a) => Grid a -> Int
nBlanks g = Dims.iter (dims g) 0 $ \acc idx -> if isBlank (getG g idx) then pure (acc + 1) else pure acc

nNonBlanks :: (Unbox a, HasBlank a) => Grid a -> Int
nNonBlanks g = Dims.iter (dims g) 0 $ \acc idx -> if nonBlank (getG g idx) then pure (acc + 1) else pure acc

nPoints g = let (Dims nRows nCols) = dims g in nRows * nCols

nonBlankFrac :: (Unbox a, HasBlank a) => Grid a -> Float
nonBlankFrac g = (fromIntegral $ nNonBlanks g)/(fromIntegral $ nPoints g)

nVal :: (Unbox a, HasBlank a) => Grid a -> a -> Int
nVal g x = Dims.iter (dims g) 0 $ \acc idx -> if (getG g idx) == x then pure (acc + 1) else pure acc

-- g1 takes precedence!
union :: (Unbox a, HasBlank a) => Grid a -> Grid a -> Maybe (Grid a)
union g1 g2 = do
  guard $ sameDims g1 g2
  pure $ fromFunc (dims g1) $ \idx -> if nonBlank (getG g1 idx) then (getG g1 idx) else (getG g2 idx)

safeUnion :: (Unbox a, HasBlank a) => Grid a -> Grid a -> Maybe (Grid a)
safeUnion g1 g2 = do
  guard $ sameDims g1 g2
  fromFuncM (dims g1) $ \idx -> do
    let x1 = getG g1 idx
    let x2 = getG g2 idx
    when (nonBlank x1 && nonBlank x2) $
      guard $ x1 == x2
    pure $ if isBlank x1 then x2 else x1

toOffset :: (Unbox a) => Grid a -> Index -> Int
toOffset g (Index i j) = i * nCols g + j

toOffsetSafe :: (Unbox a) => Grid a -> Index -> Maybe Int
toOffsetSafe g idx = do
  guard $ Dims.inBounds (dims g) idx
  pure $ toOffset g idx

getD :: (Unbox a, HasBlank a) => Grid a -> Index -> a
getD g idx =
  case toOffsetSafe g idx of
    Just i -> gridData g Vector.! i
    Nothing -> blank

get :: (Unbox a) => Grid a -> Index -> a
get g idx = gridData g Vector.! (toOffset g idx)

-- Just for this file, since we can't qualify `Grid` here
getG :: (Unbox a) => Grid a -> Index -> a
getG = Lib.Grid.get

setD :: (Unbox a) => Grid a -> a -> Index -> Grid a
setD g@(Grid gDims gData) val idx =
  case toOffsetSafe g idx of
    Just i -> Grid gDims $ gData Vector.// [(i, val)]
    Nothing -> g

set :: (Unbox a) => Grid a -> a -> Index -> Grid a
set g@(Grid gDims gData) val idx = Grid gDims $ gData Vector.// [(offset, val)]
  where
    offset = (toOffset g idx)

setPairsD :: (Unbox a) => Grid a -> [(Index, a)] -> Grid a
setPairsD g@(Grid gDims gData) pairs = runIdentity $ do
  let mappedPairs = flip Prelude.mapM pairs $ \(idx, val) ->
        case toOffsetSafe g idx of
          Just i -> pure $ (i, val)
          Nothing -> Nothing
  case mappedPairs of
    Just mPairs -> pure $ Grid gDims $ gData Vector.// mPairs
    Nothing -> pure g

-- unsafe
setPairs :: (Unbox a) => Grid a -> [(Index, a)] -> Grid a
setPairs g@(Grid gDims gData) pairs =
  let mappedPairs = flip Prelude.map pairs $ \(idx, val) -> (toOffset g idx, val) in
    Grid gDims $ gData Vector.// mappedPairs

-- unsafe
setIdxsToVal :: (Unbox a) => Grid a -> [Index] -> a -> Grid a
setIdxsToVal g@(Grid gDims gData) idxs val =
  let pairs = flip Prelude.map idxs (\idx -> (idx, val)) in
    Lib.Grid.setPairs g pairs

getRow :: (Unbox a) => Grid a -> Int -> [a]
getRow g rIdx = [getG g (Index rIdx k) | k <- range $ nCols g]

getCol :: (Unbox a) => Grid a -> Int -> [a]
getCol g cIdx = [getG g (Index k cIdx) | k <- range $ nRows g]

nonBlankRows :: (Unbox a, HasBlank a) => Grid a -> [Int]
nonBlankRows g = flip List.filter (range $ nRows g) $ \i ->
  flip any (getRow g i) $ \val -> nonBlank val

nonBlankCols :: (Unbox a, HasBlank a) => Grid a -> [Int]
nonBlankCols g = flip List.filter (range $ nCols g) $ \j ->
  flip any (getCol g j) $ \val -> nonBlank val

sameBlanks :: (Unbox a, HasBlank a) => Grid a -> Grid a -> Bool
sameBlanks g1 g2 = sameDims g1 g2 && core g1 g2
  where
    core g1 g2 = Dims.all (dims g1) $ \idx ->
      isBlank (getG g1 idx) == isBlank (getG g2 idx)

showGrid :: (Unbox a, Show a) => Grid a -> String
showGrid g =
  let header = "Grid " ++ show (nRows g) ++ " " ++ show (nCols g) ++ "\n" in
    Int.iter (nRows g) header $ \acc i ->
      acc ++ "\n" ++ (showRow g i)
  where
    showRow :: (Unbox a, Show a) => Grid a -> Int -> String
    showRow g i = Int.iter (nCols g) "" $ \acc j -> acc ++ " " ++ show (getG g (Index i j)) ++ " "

instance (Unbox a, Show a) => Show (Grid a) where
  show = showGrid

neighbors :: (Unbox a) => Grid a -> Index -> [Index]
neighbors input idx0 = do
  ax  <- [Horizontal, Vertical, DownRight, DownLeft]
  dir <- [Normal, Reverse]
  let idx = idx0 + Index.scale (Direction.toScale dir) (Axis.toDelta ax)
  guard $ Dims.inBounds (dims input) idx
  pure idx

neighborsOrtho :: (Unbox a) => Grid a -> Index -> [Index]
neighborsOrtho input idx0 = do
  ax  <- [Horizontal, Vertical]
  dir <- [Normal, Reverse]
  let idx = idx0 + Index.scale (Direction.toScale dir) (Axis.toDelta ax)
  guard $ Dims.inBounds (dims input) idx
  pure idx

neighborsDiag :: (Unbox a) => Grid a -> Index -> [Index]
neighborsDiag input idx0 = do
  ax  <- [DownRight, DownLeft]
  dir <- [Normal, Reverse]
  let idx = idx0 + Index.scale (Direction.toScale dir) (Axis.toDelta ax)
  guard $ Dims.inBounds (dims input) idx
  pure idx

showGridDiff :: Grid Color -> Grid Color -> Box.Grid String
showGridDiff g1 g2
  | sameDims g1 g2 =
    Box.fromFunc (dims g1) $ \idx ->
      if getG g1 idx == getG g2 idx
      then "  " ++ show (getG g1 idx) ++ "  "
      else "[" ++ show (getG g1 idx) ++ "|" ++ show (getG g2 idx) ++ "]"
  | otherwise = Box.const (Dims 1 1) (show (dims g1) ++ " != " ++ show (dims g2))

-- g1 is a subset of g2
subset :: (Unbox a, HasBlank a, Eq a) => Grid a -> Grid a -> Bool
subset g1 g2 = sameDims g1 g2 && subsetElems g1 g2
  where
    subsetElems g1 g2 = Dims.all (dims g1) $ \idx ->
      (nonBlank $ getG g1 idx) <= (getG g1 idx == getG g2 idx)

isNull :: (Unbox a) => Grid a -> Bool
isNull g = dims g == Dims 0 0

transpose :: (Unbox a) => Grid a -> Grid a
transpose g = fromFunc (Dims.transpose $ dims g) $ getG g . Index.transpose

sameDims :: (Unbox a) => Grid a -> Grid b -> Bool
sameDims g1 g2 = dims g1 == dims g2

beqUpto :: (Unbox a, Eq a) => Grid a -> Grid a -> Grid Bool -> Bool
beqUpto g1 g2 mask = (isNull mask && g1 == g2)
  || (sameDims g1 g2 && sameDims g1 mask && beqUptoCore g1 g2 mask)
  where
    beqUptoCore g1 g2 mask = Dims.all (dims g1) $ \idx ->
      getG mask idx || getG g1 idx == getG g2 idx

-- wherever val appears in g1, it is also val in g2
-- interpretation: g1 is input, g2 is output
subsetForVal :: (Unbox a, Eq a) => Grid a -> Grid a -> a -> Bool
-- redundant sameDims check, but helpful short circuit
subsetForVal g1 g2 val = (sameDims g1 g2) && beqUpto g1 g2 mask where
  mask = fromFunc (dims g1) $ \idx -> if (getG g1 idx) == val then False else True


allSameDims :: (Unbox a, Unbox b) => Box.Grid (Grid a) -> Box.Grid (Grid b) -> Bool
allSameDims g1 g2 = Box.sameDims g1 g2 && (Dims.all (Box.dims g1) $ \idx ->
  sameDims (Box.getG g1 idx) (Box.getG g2 idx))

uniformDims :: (Unbox a) => Box.Grid (Grid a) -> Bool
uniformDims gs =
  let innerDims = dims (Box.get gs (Index 0 0)) in
    Dims.all (Box.dims gs) $ \idx -> dims (Box.get gs idx) == innerDims

containsVal :: (Unbox a, Eq a) => a -> Grid a -> Bool
containsVal x g = Dims.any (dims g) $ \idx -> getG g idx == x

-- TODO: throw error or keep Maybe?
concatRows :: (Unbox a) => Grid a -> Grid a -> Maybe (Grid a)
concatRows g1 g2 = do
  guard $ nCols g1 == nCols g2
  pure $ fromFunc (Dims (nRows g1 + nRows g2) (nCols g2)) $ \idx@(Index i j) ->
    if i < nRows g1 then getG g1 (Index i j) else getG g2 (Index (i-nRows g1) j)

concatCols :: (Unbox a) => Grid a -> Grid a -> Maybe (Grid a)
concatCols g1 g2 = do
  guard $ nRows g1 == nRows g2
  pure $ fromFunc (Dims (nRows g1) (nCols g1 + nCols g2)) $ \idx@(Index i j) ->
    if i < nCols g1 then getG g1 (Index i j) else getG g2 (Index i (j-nCols g1))

map :: (Unbox a, Unbox b) => (Index -> a -> b) -> Grid a -> Grid b
map f g = fromFunc (dims g) $ \idx -> f idx $ getG g idx

mapM :: (Unbox a, Unbox b, Monad m) => (Index -> a -> m b) -> Grid a -> m (Grid b)
mapM f g = fromFuncM (dims g) $ \idx -> f idx $ getG g idx

filter :: (Unbox a, HasBlank a) => (Index -> a -> Bool) -> Grid a -> Grid a
filter f g = flip Lib.Grid.map g $ \idx x -> if f idx x then x else blank

upscale :: (Unbox a) => Grid a -> Dims -> Box.Grid (Grid a)
upscale g ds@(Dims km kn) = Box.fromFunc (dims g) (\idx -> Lib.Grid.const ds (getG g idx))

tile :: (Unbox a) => Grid a -> Dims -> Box.Grid (Grid a)
tile g dims = Box.fromFunc dims $ \idx -> g

-- TODO: these are pointlessly slow, better to use a Foldable/Traversable/whatever whenever needed
toList :: (Unbox a) => Grid a -> [a]
toList g = reverse $ Dims.iter (dims g) [] $ \acc idx -> pure $ (getG g idx):acc

toListWithIndices :: (Unbox a) => Grid a -> [(Index, a)]
toListWithIndices g = reverse $ Dims.iter (dims g) [] $ \acc idx -> pure $ (idx, getG g idx):acc

-----------------
-- Subgrids
-----------------

getSubgridUnsafe :: (Unbox a) => Grid a -> Dims -> Index -> Grid a
getSubgridUnsafe g dims idx0 = fromFunc dims $ \idx -> getG g (idx0 + idx)

getSubgridOpt :: (Unbox a) => Grid a -> Dims -> Index -> Maybe (Grid a)
getSubgridOpt g sgDims@(Dims dx dy) idx0@(Index i j) = do
  let Dims gx gy = dims g
  guard $ dx + i <= gx
  guard $ dy + j <= gy
  pure $ fromFunc sgDims $ \idx -> getG g (idx0 + idx)

findSubgrids :: (Unbox a) => Grid a -> Dims -> (Grid a -> Bool) -> [Index]
findSubgrids g dims2@(Dims m2 n2) p =
  let Dims m1 n1 = dims g in
    Dims.iter (Dims (m1+1-m2) (n1+1-n2)) [] $ \acc idx ->
    pure $  if p (getSubgridUnsafe g dims2 idx) then idx:acc else acc

replaceSubgridUnsafeM :: (Unbox a, Monad m) => Grid a -> Dims -> Index -> (Grid a -> m (Grid a)) -> m (Grid a)
replaceSubgridUnsafeM grid dims idx0 grid2grid =
  let subgrid = getSubgridUnsafe grid dims idx0 in
    flip Lib.Grid.mapM grid $ \idx c -> do
      if Dims.inBounds dims (idx - idx0)
        then do
          newSubgrid <- grid2grid subgrid
          pure $ Lib.Grid.get newSubgrid  (idx - idx0)
        else pure c

-----------------
-- Combinator Instances
-----------------
{-
instance Functor Grid where
  fmap :: (Unbox a) => (a -> b) -> Grid a -> Grid b
  fmap f = Lib.Grid.map (\_ -> f)

instance Foldable Grid where
  foldMap :: (Monoid m) => (a -> m) -> Grid a -> m
  foldMap f g = Dims.iter (dims g) mempty $ \acc idx -> pure $ acc <> f (getG g idx)

instance Traversable Grid where
  -- TODO: does this get used? Why not have a typeclass just for mapM and friends?
  -- Can we get away with this??
  traverse :: (Applicative m) => (a -> m b) -> Grid a -> m (Grid b)
  traverse _ _ = error "traverse not implemented for Grid"
-}
--mapM :: (Monad m) => (a -> m b) -> Grid a -> m (Grid b)
--mapM f = Lib.Grid.mapM (\_ -> f)

--sequence :: Monad m => Grid (m a) -> m (Grid a)
--sequence g = fromFuncM (dims g) $ getG g

-----------------
-- Partitioning
-----------------

type UnpartitionFn a = Box.Grid (Grid a) -> Grid a

partitionEven :: (Unbox a) => Dims -> Dims -> Grid a -> Maybe (Box.Grid (Grid a))
partitionEven outerDims@(Dims mOut nOut) innerDims@(Dims mIn nIn) g = do
  guard $ nRows g == mOut * mIn
  guard $ nCols g == nOut * nIn
  pure $ Box.fromFunc outerDims $ \(Index i j) -> getSubgridUnsafe g innerDims (Index (i * mIn) (j * nIn))

partitionEvenOuterDims :: (Unbox a) => Dims -> Grid a -> Maybe (Box.Grid (Grid a))
partitionEvenOuterDims dims@(Dims m n) g = do
  guard $ mod (nRows g) m == 0
  guard $ mod (nCols g) n == 0
  partitionEven dims (Dims (div (nRows g) m) (div (nCols g) n)) g

partitionEvenInnerDims :: (Unbox a) => Dims -> Grid a -> Maybe (Box.Grid (Grid a))
partitionEvenInnerDims dims@(Dims m n) g = do
  guard $ mod (nRows g) m == 0
  guard $ mod (nCols g) n == 0
  partitionEven (Dims (div (nRows g) m) (div (nCols g) n)) dims g

unpartitionEven :: (Unbox a) => Box.Grid (Grid a) -> Maybe (Grid a)
unpartitionEven gs = do
  let innerDims = dims (Box.getG gs (Index 0 0))
  guard $ Dims.all (Box.dims gs) $ \idx -> dims (Box.getG gs idx) == innerDims
  let Dims mIn nIn = innerDims
  let newDims = Dims (Box.nRows gs * mIn) (Box.nCols gs * nIn)
  pure $ fromFunc newDims $ \(Index i j) ->
    let g = Box.getG gs $ Index (div i mIn) (div j nIn) in
      getG g $ Index (mod i mIn) (mod j nIn)


data RePartitionData = RePartitionData { structure :: Grid (Dims, Index) }

-- TODO: this and others that are unsafe may cause problems!
-- Worth always returning maybes?
rePartitionNoSepWith :: (Unbox a) => Grid a -> RePartitionData -> Maybe (Box.Grid (Grid a))
rePartitionNoSepWith g (RePartitionData structure) = do
  let outerDims = dims structure
  Box.fromFuncM outerDims $ \outerIdx -> do
    let (innerDims, oldIdx) = getG structure outerIdx
    getSubgridOpt g innerDims oldIdx

computeRePartitionData :: (Unbox a) => Box.Grid (Grid a) -> Maybe RePartitionData
computeRePartitionData gs = do
  guard $ Int.all (Box.nRows gs) $ \i -> Int.allSame (Box.nCols gs) $ \j -> nRows (Box.getG gs (Index i j))
  guard $ Int.all (Box.nCols gs) $ \j -> Int.allSame (Box.nRows gs) $ \i -> nCols (Box.getG gs (Index i j))
  let nRowList = Prelude.map (\i -> nRows (Box.getG gs (Index i 0))) (List.range $ Box.nRows gs)
  let nColList = Prelude.map (\j -> nCols (Box.getG gs (Index 0 j))) (List.range $ Box.nCols gs)
  let rowOffsets = 0 : scanl1 (+) nRowList
  let colOffsets = 0 : scanl1 (+) nColList
  pure $ RePartitionData $ fromFunc (Dims (length nRowList) (length nColList)) $ \idx@(Index i j) ->
    let innerDims :: Dims = dims (Box.getG gs idx)
        innerIdx :: Index = Index (rowOffsets List.!! i) (colOffsets List.!! j)
    in
      (innerDims, innerIdx)

unpartitionNoSep :: (Unbox a) => Box.Grid (Grid a) -> Maybe (Grid a)
unpartitionNoSep gs = do
  guard $ Int.all (Box.nRows gs) $ \i -> Int.allSame (Box.nCols gs) $ \j -> nRows (Box.getG gs (Index i j))
  guard $ Int.all (Box.nCols gs) $ \j -> Int.allSame (Box.nRows gs) $ \i -> nCols (Box.getG gs (Index i j))
  let nRowList = Prelude.map (\i -> nRows (Box.getG gs (Index i 0))) (List.range $ Box.nRows gs)
  let nColList = Prelude.map (\j -> nCols (Box.getG gs (Index 0 j))) (List.range $ Box.nCols gs)
  let rowOffsets = scanl1 (+) nRowList
  let colOffsets = scanl1 (+) nColList
  pure $ fromFunc (Dims (sum nRowList) (sum nColList)) $ \(Index i j) -> runIdentity $ do
    let Just (iOuter, iInner) = flip List.first (zip3 [0..] (0:init rowOffsets) rowOffsets) $ \(iOuter, start, end) ->
          if i >= start && i < end then Just (iOuter, i - start) else Nothing
    let Just (jOuter, jInner) = flip List.first (zip3 [0..] (0:init colOffsets) colOffsets) $ \(jOuter, start, end) ->
          if j >= start && j < end then Just (jOuter, j - start) else Nothing
    let g = Box.getG gs (Index iOuter jOuter)
    pure $ getG g (Index iInner jInner)

data PartitionSepData = PartitionSepData { hLines :: [Int], vLines :: [Int] } deriving (Eq, Ord, Show)

sameUnpartitionSep :: (Unbox a, HasBlank a) => PartitionSepData -> Grid a -> Grid a -> Bool
sameUnpartitionSep pData g1 g2 =
  sameDims g1 g2
  && List.all (\i -> Int.all (nCols g1) (\j -> getG g1 (Index i j) == getG g2 (Index i j))) (hLines pData)
  && List.all (\j -> Int.all (nRows g1) (\i -> getG g1 (Index i j) == getG g2 (Index i j))) (vLines pData)

unpartitionSep :: (Unbox a, HasBlank a) => Grid a -> PartitionSepData -> Box.Grid (Grid a) -> Maybe (Grid a)
unpartitionSep g0 (PartitionSepData hLines vLines) gs = do
  guard $ Int.all (Box.nRows gs) $ \i -> Int.allSame (Box.nCols gs) $ \j -> nRows (Box.getG gs (Index i j))
  guard $ Int.all (Box.nCols gs) $ \j -> Int.allSame (Box.nRows gs) $ \i -> nCols (Box.getG gs (Index i j))
  let rowStartCounts = computeSepStartCounts (nRows g0) hLines
  let colStartCounts = computeSepStartCounts (nCols g0) vLines
  pure $ fromFunc (dims g0) $ \idx@(Index i j) ->
    if elem i hLines || elem j vLines then getG g0 idx else
      let (outerRow, innerRow) = findOffsets rowStartCounts i
          (outerCol, innerCol) = findOffsets colStartCounts j in
        getG (Box.getG gs (Index outerRow outerCol)) (Index innerRow innerCol)
    where
      findOffsets :: [(Int, Int)] -> Int -> (Int, Int)
      findOffsets rowStartCounts i =
        Maybe.fromJust $ List.first (\(outerRow, (rowStart, nRows)) -> do
              guard $ rowStart <= i && i < rowStart + nRows
              pure (outerRow, i - rowStart)) (List.zip [0..] rowStartCounts)

partitionSepWith :: (Unbox a, HasBlank a) => Grid a -> PartitionSepData -> Maybe (Box.Grid (Grid a))
partitionSepWith g (PartitionSepData hLines vLines) = do
  let rowStartCounts = computeSepStartCounts (nRows g) hLines
  let colStartCounts = computeSepStartCounts (nCols g) vLines
  guard $ length rowStartCounts > 0 && length colStartCounts > 0
  let gs = Box.fromFunc (Dims (length rowStartCounts) (length colStartCounts)) $ \(Index i j) ->
        let (rowStart, nRows) = rowStartCounts List.!! i
            (colStart, nCols) = colStartCounts List.!! j in
          getSubgridUnsafe g (Dims nRows nCols) (Index rowStart colStart)
  pure gs

computeSepStartCounts :: Int -> [Int] -> [(Int, Int)]
computeSepStartCounts k lines =
  let segments = List.zip ([-1] ++ lines) (lines ++ [k]) in
    Prelude.map (\(start, next) -> (start + 1, next-start-1)) $ List.filter (\(start, next) -> next > start + 1) segments

-----------------
-- Coloring Utilities
-----------------

changeVal :: (Unbox a, Eq a) => Grid a -> a -> a -> Grid a
changeVal g val1 val2 = flip Lib.Grid.map g $ \_ val -> if val == val1 then val2 else val

swapVals :: (Unbox a, Eq a) => Grid a -> a -> a -> Grid a
swapVals g val1 val2 = flip Lib.Grid.map g $ \_ val ->
  if val == val1 then val2
  else if val == val2 then val1
  else val

distinctValsInGrids :: (Unbox a, Eq a, Ord a) => (a -> Bool) -> [Grid a] -> Set a
distinctValsInGrids f gs = List.reduce (Set.union) id $ flip Prelude.map gs (\g -> distinctVals f g)

pickColor :: (Unbox a, Monad m, Eq a, Ord a, HasBlank a) => SearchT m (Grid a -> Maybe a)
pickColor = do
  choice "Grid.pickColor" [
    ("majorityVal", pure (\g -> do
        let gMajority = fst (majorityVals g)
        guard $ (length gMajority) == 1
        pure $ head gMajority))
    , ("minorityVal", pure (\g -> do
        let gMinority = fst (minorityVals g)
        guard $ (length gMinority) == 1
        pure $ head gMinority))
    , ("majorityNonBlankVal", pure (\g -> do
        let (gMajority, maxCount) = majorityNonBlankVals g
        guard $ (length gMajority) == 1 && maxCount > 0
        pure $ head gMajority))
    , ("minorityNonBlankVal", pure (\g -> do
        let (gMinority, minCount) = minorityNonBlankVals g
        guard $ (length gMinority) == 1 && minCount > 0
        pure $ head gMinority))
    ]


-- FIXME: should this just be StdGoal -> SearchT m (Ex Color)?
enumRelevantColors :: (Monad m, HasTrainTest m, HasSynth1Context m Color) =>
  Ex (Grid Color) -> Ex.ForTrain (Grid Color) -> SearchT m (Ex Color)
enumRelevantColors inputs outputs = choice "enumRelevantColors" [
  ("ctx",     synthCtx)
  , ("noCtx", do
      let distinctColors = distinctValsInGrids (\_ -> True) $ (Ex.toBigList inputs) ++ outputs
      c <- oneOf "Color.enumVals" $ flip Prelude.map (Data.Foldable.toList distinctColors) $ \k -> (show k, k)
      Ex.map (\_ -> c) <$> getDummyEx)
  , ("func", do
      phi <- pickColor
      (mappedColors :: Ex Color) <- liftO $ flip Ex.mapM inputs (\ig -> phi ig)
      pure $ mappedColors)
  ]


{-|
enumRelevantInts :: Ex (Grid Color) -> [([Char], Int, Maybe (Ex Int))]
enumRelevantInts inputs = [
  ("m - 1", 0, pure $ Ex.map (\ig -> (Lib.Grid.nRows ig) - 1) inputs)
  , ("n - 1", 0, pure $ Ex.map (\ig -> (Lib.Grid.nCols ig) - 1) inputs)
  , ("middleRow", 1, do
        guard $ flip Ex.all inputs $ \ig -> ((Lib.Grid.nRows ig) `mod` 2) == 1
        pure $ flip Ex.map inputs $ \ig -> ((Lib.Grid.nRows ig) `div` 2) + 1)
  , ("middleCol", 1, do
        guard $ flip Ex.all inputs $ \ig -> ((Lib.Grid.nCols ig) `mod` 2) == 1
        pure $ flip Ex.map inputs $ \ig -> ((Lib.Grid.nCols ig) `div` 2) + 1)
  , ("nDistinctVals", 2, pure $ Ex.map (\ig -> Lib.Grid.nDistinctVals (\_ -> True) ig) inputs)
  , ("nDistinctNonBlanks", 2, pure $ Ex.map (\ig -> Lib.Grid.nDistinctVals nonBlank ig) inputs)
  ]
-}


enumRelevantInts :: (Monad m) => Ex (Grid Color) -> SearchT m (Ex Int)
enumRelevantInts inputs = choice "enumRelevantInts" [
  ("m - 1", pure $ Ex.map (\ig -> (Lib.Grid.nRows ig) - 1) inputs)
  , ("n - 1", pure $ Ex.map (\ig -> (Lib.Grid.nCols ig) - 1) inputs)
  , ("middleRow", do
        guard $ flip Ex.all inputs $ \ig -> ((Lib.Grid.nRows ig) `mod` 2) == 1
        pure $ flip Ex.map inputs $ \ig -> ((Lib.Grid.nRows ig) `div` 2) + 1)
  , ("middleCol", do
        guard $ flip Ex.all inputs $ \ig -> ((Lib.Grid.nCols ig) `mod` 2) == 1
        pure $ flip Ex.map inputs $ \ig -> ((Lib.Grid.nCols ig) `div` 2) + 1)
  , ("nDistinctVals", pure $ Ex.map (\ig -> Lib.Grid.nDistinctVals (\_ -> True) ig) inputs)
  , ("nDistinctNonBlanks", pure $ Ex.map (\ig -> Lib.Grid.nDistinctVals nonBlank ig) inputs)
  ]

-----------------
-- Features
-----------------

rowIsUniform :: (Unbox a, Eq a) => Grid a -> Int -> Maybe a
rowIsUniform g i = do
  guard $ Int.allSame (nCols g) $ \j -> getG g (Index i j)
  pure $ getG g (Index i 0)

colIsUniform :: (Unbox a, Eq a) => Grid a -> Int -> Maybe a
colIsUniform g j = do
  guard $ Int.allSame (nRows g) $ \i -> getG g (Index i j)
  pure $ getG g (Index 0 j)

isUniform :: (Unbox a, Eq a) => Grid a -> Maybe a
isUniform g = do
  guard $ Int.allSame (nRows g * nCols g) $ \i -> getG g (Dims.int2index (dims g) i)
  pure $ getG g (Index 0 0)

firstVal :: (Unbox a, Eq a) => (a -> Bool) -> Grid a -> Maybe a
firstVal p g = Dims.first (dims g) $ \idx -> pure $ do
  guard $ p (getG g idx)
  pure $ getG g idx

isSquare  :: (Unbox a) => Grid a -> Maybe Int
isSquare g = do
  guard $ nRows g == nCols g
  pure $ nRows g

reflectAround :: (Unbox a) => Grid a -> Axis -> Grid a
reflectAround g ax = flip Lib.Grid.map g $ \idx _ -> getG g (Axis.reflectAround (dims g) ax idx)

isSymmetricAround :: (Unbox a, Eq a) => Axis -> Grid a -> Bool
isSymmetricAround ax g = Dims.all (dims g) $ \idx -> getG g idx == getG g (Axis.reflectAround (dims g) ax idx)

distinctVals :: (Unbox a, Eq a, Ord a) => (a -> Bool) -> Grid a -> Set a
distinctVals p g = Dims.iter (dims g) Set.empty $ \acc idx -> pure $
  if p (getG g idx) then Set.insert (getG g idx) acc else acc

nDistinctVals :: (Unbox a, Eq a, Ord a) => (a -> Bool) -> Grid a -> Int
nDistinctVals p g = Set.size $ distinctVals p g

buildCounts :: (Unbox a, Eq a, Ord a) => (a -> Bool) -> Grid a -> Map a Int
buildCounts p g = Dims.iter (dims g) Map.empty $ \acc idx ->
  let x = getG g idx in
    pure $ if p x then Map.insertWith (+) x 1 acc else acc

maxValCount :: (Unbox a, Eq a, Ord a) => (a -> Bool) -> Grid a -> Int
maxValCount p g = maximum . (0:) . Map.elems $ buildCounts p g

nNonBlankVals :: (Unbox a, HasBlank a) => Grid a -> Int
nNonBlankVals g = Dims.iter (dims g) 0 $ \acc idx ->
  pure $ if nonBlank (getG g idx) then acc + 1 else acc

predIdxs :: (Unbox a) => Grid a -> (Index -> a -> Bool) -> Set Index
predIdxs g f = Dims.iter (dims g) Set.empty $ \acc idx ->
  pure $ if f idx (getG g idx) then Set.insert idx acc else acc

nonBlankIdxs :: (Unbox a, HasBlank a) => Grid a -> Set Index
nonBlankIdxs g = predIdxs g (\_ val -> nonBlank val)

valIdxs :: (Unbox a, Eq a) => Grid a -> a -> Set Index
valIdxs g val = Dims.iter (dims g) Set.empty $ \acc idx ->
  pure $ if (getG g idx) == val then Set.insert idx acc else acc

majorityVals :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> ([a], Int)
majorityVals g =
  let counts = Map.toList $ buildCounts (\_ -> True) g in
    let biggestCount = snd $ List.maximumBy (\(c1, k1) (c2, k2) -> compare k1 k2) counts in
      (Prelude.map fst $ List.filter (\(_, count) -> count == biggestCount) counts, biggestCount)

minorityVals :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> ([a], Int)
minorityVals g =
  let counts = Map.toList $ buildCounts (\_ -> True) g in
    let smallestCount = snd $ List.minimumBy (\(c1, k1) (c2, k2) -> compare k1 k2) counts in
      (Prelude.map fst $ List.filter (\(_, count) -> count == smallestCount) counts, smallestCount)

majorityNonBlankVals :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> ([a], Int)
majorityNonBlankVals g =
  let counts = Map.toList $ buildCounts nonBlank g in
    if null counts then ([blank], 0) else
      let biggestCount = snd $ List.maximumBy (\(c1, k1) (c2, k2) -> compare k1 k2) counts in
        (Prelude.map fst $ List.filter (\(_, count) -> count == biggestCount) counts, biggestCount)

majorityNonBlankVal :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> Maybe a
majorityNonBlankVal g = case majorityNonBlankVals g of
  ([x], _) -> pure x
  _ -> Nothing

minorityNonBlankVals :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> ([a], Int)
minorityNonBlankVals g =
  let counts = Map.toList $ buildCounts nonBlank g in
    if null counts then ([blank], 0) else
      let smallestCount = snd $ List.minimumBy (\(c1, k1) (c2, k2) -> compare k1 k2) counts in
        (Prelude.map fst $ List.filter (\(_, count) -> count == smallestCount) counts, smallestCount)

minorityNonBlankVal :: (Unbox a, Eq a, Ord a, HasBlank a) => Grid a -> Maybe a
minorityNonBlankVal g = case minorityNonBlankVals g of
  ([x], _) -> pure x
  _ -> Nothing

-- TODO: result in SearchT?
mapBinOp :: (Unbox a) => (a -> a -> a) -> Grid a -> Grid a -> Grid a
mapBinOp f g1 g2 =
  if dims g1 == dims g2
  then fromFunc (dims g1) $ \idx -> f (getG g1 idx) (getG g2 idx)
  else error "mapBinOp called with bad dims"

map3Op1 :: (Unbox a) => (a -> a -> a -> a) -> Grid a -> Grid a -> Grid a
map3Op1 f g1 g2 =
  if dims g1 == dims g2
  then fromFunc (dims g1) $ \idx -> f (getG g1 idx) (getG g1 idx) (getG g2 idx)
  else error "map3Op1 called with bad dims"


-- TODO: parameterize by ordering
--reduceBinOp :: (a -> a -> a) -> Grid a -> a
--reduceBinOp f g =
--  let x0 = getG g (Index 0 0) in
--    Dims.iter (dims g) x0 $ \acc idx ->
--                              pure $ if idx == Index 0 0 then acc else f acc (getG g idx)

reduceBinOp :: (Unbox a) => (a -> a -> a) -> Grid a -> [Index] -> a
reduceBinOp f g ordering =
    List.reduce (\acc val -> f acc val) (\idx -> getG g idx) ordering



-- TODO: move to features as it is specialized to color?
-- TODO: is Data.Foldable.toList too slow? Is using Set wrong here?
-- FIXME: do we want to use Axis.orthoDist?
-- the nearest val that ISNT YOUR VAL
nearestNonSelfVal :: Grid Color -> Grid Color
nearestNonSelfVal g =
  let nonSelfNonBlanks :: Map Color (Set Index) = List.iter distinctGridVals Map.empty $ \acc val ->
        pure $ Map.insert val (flip Set.filter gridNonBlanks (\idx -> (getG g idx) /= val)) acc in
    fromFunc (dims g) $ \idx ->
      let nonValNonBlanks :: Set Index = Maybe.fromJust $ Map.lookup (getG g idx) nonSelfNonBlanks in
        if null nonValNonBlanks then blank
        else
          let closestIdxs :: [Index] = List.argminsKey (\idx2 -> Axis.dist OrthoDist idx idx2) (Set.toList nonValNonBlanks) in
            if length closestIdxs == 1 || List.allSame (flip Prelude.map closestIdxs (\idx -> getG g idx))
            then getG g (closestIdxs !! 0) else blank
  where
      gridNonBlanks = Lib.Grid.nonBlankIdxs g -- we don't consider blanks
      distinctGridVals = Set.toList $ distinctVals (\_ -> True) g

-- in this feature, you are allowed to be yourself! (so, all non-blanks will be themselves)
nearestNonBlank :: Grid Color -> Grid Color
nearestNonBlank g =
  -- if all blank then blank
  if Lib.Grid.allBlank g then g
  -- if only have one distinct nonblank, then const grid of that nonblank
  else if (Lib.Grid.nDistinctVals nonBlank g) == 1 then Lib.Grid.const (dims g) (Set.elemAt 0 (distinctVals nonBlank g))
  else
  fromFunc (dims g) $ \idx ->
    if null gridNonBlanks then blank
    else
      let closestIdxs = List.argminsKey (\idx2 -> Axis.dist OrthoDist idx idx2) gridNonBlanks in
        if length closestIdxs == 1 || List.allSame (flip Prelude.map closestIdxs (\idx -> getG g idx))
        then getG g (closestIdxs !! 0) else blank
  where
      gridNonBlanks = Set.toList (Lib.Grid.nonBlankIdxs g) -- we don't consider blanks

-- the nearest non-blank that isn't at your index!
nearestNonSelfIdx :: Grid Color -> Grid Color
nearestNonSelfIdx g =
  -- if all blank then blank
  if Lib.Grid.allBlank g then g else
    let gridNonBlanks = Set.toList (Lib.Grid.nonBlankIdxs g) in -- we don't consider blanks
      fromFunc (dims g) $ \idx ->
        if null gridNonBlanks then blank else
          case Prelude.filter (\idx2 -> idx /= idx2) gridNonBlanks of
            [] -> blank
            xs ->
              let closestIdxs = List.argminsKey (\idx2 -> Axis.dist OrthoDist idx idx2) xs in
                if length closestIdxs == 1 || List.allSame (flip Prelude.map closestIdxs (\idx -> getG g idx))
                then getG g (closestIdxs !! 0) else blank


extremeNonBlankDistances :: (Monad m) => Ex (Grid Color) -> SearchT m (Ex (Grid Int))
extremeNonBlankDistances inputs = do
  -- ensure that each input grid has at least one non-blank (not always true!)
  guard $ flip Ex.all inputs $ \ig -> not (Lib.Grid.allBlank ig)
  -- guard that there aren't too many non-blanks (currently 1/3, which is fairly strict)
  guard $ flip Ex.all inputs $ \ig -> (Lib.Grid.nNonBlanks ig) < ((Dims.nCells (dims ig)) `div` 3)
  distFunc <- oneOf "extremeNonBlankDistances.distFunc" [("ortho", Axis.dist OrthoDist), ("diag", Axis.dist DiagDist)]
  extreme <- oneOf "extremeNonBlankDistances.extreme" [("max", 1), ("min", -1)]
  pure $ flip Ex.map inputs $ \ig -> Lib.Grid.extremeDistToNonBlank
    (\idx1 idx2 -> extreme * (distFunc idx1 idx2)) ig


extremeBlankDistances :: (Monad m) => Ex (Grid Color) -> SearchT m (Ex (Grid Int))
extremeBlankDistances inputs = do
  -- ensure that each input grid has at least one non-blank (not always true!)
  guard $ flip Ex.all inputs $ \ig -> containsVal blank ig
  -- TODO: currently not guarding that there is some amoutn of nonBlanks to limit perf
  distFunc <- oneOf "extremeBlankDistances.distFunc" [("ortho", Axis.dist OrthoDist), ("diag", Axis.dist DiagDist)]
  -- currently just using min, not max
  extreme <- oneOf "extremeBlankDistances.extreme" [("min", -1)]
  pure $ flip Ex.map inputs $ \ig -> Lib.Grid.extremeDistToBlank
    (\idx1 idx2 -> extreme * (distFunc idx1 idx2)) ig

-- this is only Maybe Int instead of Int because we want to allow a grid not having the color at all
extremeDistancesToVal :: (Monad m) => Ex (Grid Color) -> Ex Color -> SearchT m (Ex (Grid (Maybe Int)))
extremeDistancesToVal inputs cs = do
  -- note we check the majority rather than all
  -- check that the majority ofe inputs have this color
  guard $ flip List.majority (Ex.toBigList (Ex.zip inputs cs)) $ \(ig, c) -> containsVal c ig
  distFunc <- oneOf "extremeDistancesToVal.distFunc" [("ortho", Axis.dist OrthoDist), ("diag", Axis.dist DiagDist)]
  extreme <- oneOf "extremeDistancesToVal.extreme" [("max", 1), ("min", -1)]
  pure $ flip Ex.map (Ex.zip inputs cs) $ \(ig, c) ->
    -- only have to do this because of majority rather than all check
    if not (containsVal c ig) then Lib.Grid.const (dims ig) Nothing else
      -- inefficient
      Lib.Grid.map (\idx val -> Just val) $ Lib.Grid.extremeDistToVal (\idx1 idx2 -> extreme * (distFunc idx1 idx2)) ig c


-- note use of getD
nNeighborsAxDirs :: (Unbox a, HasBlank a) => Grid a -> [(Axis, Direction)] -> Index -> Int
nNeighborsAxDirs g axDirs idx = flip List.count axDirs $ \(ax, dir) ->
  let idxInAxDir = Direction.step idx 1 ax dir in
    nonBlank (getD g idxInAxDir)


-- note use of getD
-- distinct non-blank colors among immediate neighbors
nNeighborColorsAxDirs :: (Unbox a, Ord a, HasBlank a) => Grid a -> [(Axis, Direction)] -> Index -> Int
nNeighborColorsAxDirs g axDirs idx = List.countDistinct id (List.filter (\x -> nonBlank x) neighborColors) where
  neighborColors = flip List.map axDirs $ \(ax, dir) -> getD g (Direction.step idx 1 ax dir)



-- how to make this quadratic?
isSurrounded :: (Unbox a, HasBlank a) => Grid a -> Grid Bool
isSurrounded g = flip Lib.Grid.map g $ \idx _ -> (nNeighborsAxDirs g axDirs idx) == 8 where
  axDirs =
        [(ax, dir) | ax <- [Horizontal, Vertical, DownRight, DownLeft], dir <- [Normal, Reverse]]

----------------------
-- enumMaybeIndices
----------------------
-- TODO: handle "group" variants of this, where the predicate itself is determined per-example.
-- TODO: some typeclass for this
-- Note: motivated by 6d0160f0

findIndices :: (Unbox a) => (a -> Bool) -> Grid a -> [Index]
findIndices p g = Dims.iter (dims g) [] $ \acc idx ->
  pure $ if p (getG g idx) then idx:acc else acc

enumMaybeIndices :: (Monad m, HasSynth1Context m Color) => SearchT m (Ex (Grid Color -> [Index]))
enumMaybeIndices = choice "Grid.enumMaybeIndices" [
  ("ofColor", Ex.map (\c -> \g -> findIndices (==c) g) <$> enumColorsCtx)
  ]

enumColorSets :: (Monad m) => SearchT m (Grid Color -> Set Color)
enumColorSets = choice "Grid.enumColorSets" [
  ("distinctNonBlankVals", pure $ \g -> distinctVals nonBlank g)
  ]


enumGridPreserving :: (Unbox a, Monad m) => SearchT m (Grid a -> Grid a)
enumGridPreserving = oneOf "Grid.enumPreservingTrans" [
  ("id", id),
  ("reflectHorizontal", flip Lib.Grid.reflectAround Horizontal),
  ("reflectVertical", flip Lib.Grid.reflectAround Vertical)
  ]
----------------------
-- Line
----------------------

-- TODO: upto mask?
-- TODO: get all lines, greedily, upto mask?
-- TODO: blanks? guarantee that adjacent lines have the same color?
horizontalLines :: (Unbox a, HasBlank a, Eq a) => Grid a -> [Int]
horizontalLines g = flip List.filter (range $ nRows g) $ \i ->
  let x = getG g (Index i 0) in
    (x /= blank) && (Int.all (nCols g) $ \j -> getG g (Index i j) == x)

verticalLines :: (Unbox a, HasBlank a, Eq a) => Grid a -> [Int]
verticalLines g = flip List.filter (range $ nCols g) $ \j ->
  let x = getG g (Index 0 j) in
    (x /= blank) && (Int.all (nRows g) $ \i -> getG g (Index i j) == x)

getDominantElem :: (Unbox a, Eq a, Ord a, Show a) => [a] -> Float -> Maybe a
getDominantElem r frac = do
  guard . not . null $ r
  let domElems = maximumBy (comparing length) . List.group $ (List.sort r)
  guard . not . null $ domElems
  let domElemFrac = (fromIntegral $ length domElems)/(fromIntegral $ length r)
  guard (frac <= domElemFrac)
  pure . head $ domElems

existsDominantElem :: (Unbox a, Eq a, Ord a, Show a) => [a] -> Float -> Bool
existsDominantElem r frac = isJust $ getDominantElem r frac

fuzzyHorizontalLines :: (Unbox a, HasBlank a, Eq a, Show a, Ord a) => Grid a -> Float -> [Int]
fuzzyHorizontalLines g frac = flip List.filter (range $ nRows g) $ \i ->
  existsDominantElem (getRow g i) frac

fuzzyVerticalLines :: (Unbox a, HasBlank a, Eq a, Show a, Ord a) => Grid a -> Float -> [Int]
fuzzyVerticalLines g frac = flip List.filter (range $ nCols g) $ \j ->
  existsDominantElem (getCol g j) frac

horizontalLinesColor :: (Unbox a, HasBlank a, Eq a) => a -> Grid a -> [Int]
horizontalLinesColor x0 g = flip List.filter (range $ nRows g) $ \i ->
  let x = getG g (Index i 0) in
    (x == x0) && (Int.all (nCols g) $ \j -> getG g (Index i j) == x)

verticalLinesColor :: (Unbox a, HasBlank a, Eq a) => a -> Grid a -> [Int]
verticalLinesColor x0 g = flip List.filter (range $ nCols g) $ \j ->
  let x = getG g (Index 0 j) in
    (x == x0) && (Int.all (nRows g) $ \i -> getG g (Index i j) == x)

lineBoolVals :: (Unbox a) => Grid a -> ([a] -> Bool) -> Axis -> Map Int Bool
lineBoolVals g f ax =
  List.iter (range (Line.numAxLines (dims g) ax)) Map.empty $ \acc ident ->
    let lineVals = Prelude.map (\idx -> getG g idx) $ Line.idxsOfId (dims g) ax ident in
      pure $ Map.insert ident (f lineVals) acc

-- FIXME: generalize with lineBoolVals
lineIntVals :: (Unbox a) => Grid a -> ([a] -> Int) -> Axis -> Map Int Int
lineIntVals g f ax =
  List.iter (range (Line.numAxLines (dims g) ax)) Map.empty $ \acc ident ->
    let lineVals = Prelude.map (\idx -> getG g idx) $ Line.idxsOfId (dims g) ax ident in
      pure $ Map.insert ident (f lineVals) acc


-- FIXME: generalize with lineBoolVals
lineColorVals :: (Unbox a) => Grid a -> ([a] -> Color) -> Axis -> Map Int Color
lineColorVals g f ax =
  List.iter (range (Line.numAxLines (dims g) ax)) Map.empty $ \acc ident ->
    let lineVals = Prelude.map (\idx -> getG g idx) $ Line.idxsOfId (dims g) ax ident in
      pure $ Map.insert ident (f lineVals) acc


lineIdxsP :: (Unbox a, HasBlank a) => Grid a -> (Index -> a -> Bool) -> Axis -> Direction -> Int -> [Index]
lineIdxsP g f ax dir ident =
  let predIdxs = flip List.filter (Line.idxsOfId (dims g) ax ident) $ \idx -> f idx (getG g idx) in
    if dir == Reverse then reverse predIdxs else predIdxs

nonBlankLineIdxs :: (Unbox a, HasBlank a) => Grid a -> Axis -> Direction -> Int -> [Index]
nonBlankLineIdxs g ax dir ident = lineIdxsP g (\idx val -> nonBlank val) ax dir ident

blankLineIdxs :: (Unbox a, HasBlank a) => Grid a -> Axis -> Direction -> Int -> [Index]
blankLineIdxs g ax dir ident = lineIdxsP g (\idx val -> isBlank val) ax dir ident

valLineIdxs :: (Unbox a, HasBlank a, Eq a) => Grid a -> a -> Axis -> Direction -> Int -> [Index]
valLineIdxs g x ax dir ident = lineIdxsP g (\idx val -> val == x) ax dir ident

axisBlank :: (Unbox a, HasBlank a) => Grid a -> Axis -> Grid Bool
axisBlank g ax =
  let vals :: Map Int Bool = lineBoolVals g (\lineVals -> flip Prelude.all lineVals $ \val -> isBlank val) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals

axHasVal :: (Unbox a, HasBlank a) => Grid a -> a -> Axis -> Grid Bool
axHasVal g x ax =
  let vals :: Map Int Bool = lineBoolVals g (\lineVals -> flip Prelude.any lineVals $ \val -> val == x) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals


nInAxis :: (Unbox a, HasBlank a, Ord a, Eq a) => Grid a -> Axis -> Grid Int
nInAxis g ax =
  let vals :: Map Int Int = lineIntVals g (\lineVals -> List.count nonBlank lineVals) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals

nBlankInAxis :: (Unbox a, HasBlank a, Ord a, Eq a) => Grid a -> Axis -> Grid Int
nBlankInAxis g ax =
  let vals :: Map Int Int = lineIntVals g (\lineVals -> List.count isBlank lineVals) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals

idxInAxis :: Grid a -> Index -> Axis -> Grid Bool
idxInAxis g idx ax =
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
      identOfIdx :: Int = idxMapper idx in
    fromFunc (dims g) $ \idx2 -> if (idxMapper idx2) == identOfIdx then True else False

idxInAxDir :: (Unbox a) => Grid a -> Index -> Axis -> Direction -> Grid Bool
idxInAxDir g idx ax dir =
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
      identOfIdx :: Int = idxMapper idx in
    fromFunc (dims g) $ \idx2 ->
      if (idxMapper idx2) == identOfIdx && Direction.precedes ax dir idx2 idx then True else False

anyIdxInAxDir :: (Unbox a) => Grid a -> [Index] -> Axis -> Direction -> Grid Bool
anyIdxInAxDir g idxs ax dir =
  List.reduce (\g1 g2 -> mapBinOp (Blank.orD True) g1 g2) (\idx -> idxInAxDir g idx ax dir) idxs


axMax :: Grid Color -> Axis -> Grid Color
axMax g ax =
  let vals :: Map Int Color = lineColorVals g (\lineVals ->
        flip List.argmaxKey (List.nub lineVals) $ \val ->
          if val == blank then 0 else (List.count (\val2 -> val2 == val) lineVals)) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals


nDistinctInAxis :: (Unbox a, Ord a, Eq a) => Grid a -> Axis -> Grid Int
nDistinctInAxis g ax =
  let vals :: Map Int Int = lineIntVals g (\lineVals -> List.countDistinct id lineVals) ax
      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in
    fromFunc (dims g) $ \idx -> Maybe.fromJust $ Map.lookup (idxMapper idx) vals


nearestValInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid a
nearestValInAxDir g ax dir =
  let axesNonBlanks :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
        nonBlankLineIdxs g ax dir ident

      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
    fromFunc (dims g) $ \idx ->
      case flip List.first (axesNonBlanks !! (idxMapper idx)) $ \idx2 ->
        if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing of
        Nothing -> blank
        Just idx2 -> getG g idx2

furthestValInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid a
furthestValInAxDir g ax dir =
  let axesNonBlanks :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
        nonBlankLineIdxs g ax (Direction.reverse dir) ident

      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
    fromFunc (dims g) $ \idx ->
      case flip List.first (axesNonBlanks !! (idxMapper idx)) $ \idx2 ->
        if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing of
        Nothing -> blank
        Just idx2 -> getG g idx2



idxOfNearestInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid (Maybe Index)
idxOfNearestInAxDir g ax dir =
  let axesNonBlanks :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
        nonBlankLineIdxs g ax dir ident

      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

    -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
    fromFunc (dims g) $ \idx ->
      flip List.first (axesNonBlanks !! (idxMapper idx)) $ \idx2 ->
        if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing



-- note the use of diagDist rather than orthoDist because we know we will be in the same axDir
distToNearestNonBlankInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid (Maybe Int)
distToNearestNonBlankInAxDir g ax dir =
  let axesNonBlanks :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
        nonBlankLineIdxs g ax dir ident

      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
    fromFunc (dims g) $ \idx ->
      case flip List.first (axesNonBlanks !! (idxMapper idx)) $ \idx2 ->
        if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing of
        Nothing -> Nothing
        Just idx2 -> Just $ Axis.dist DiagDist idx idx2

-- duplicate code with distToNearestNonBlankInAxDir
-- note the use of diagDist rather than orthoDist because we know we will be in the same axDir
distToNearestBlankInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid (Maybe Int)
distToNearestBlankInAxDir g ax dir =
  let axesBlanks :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
        blankLineIdxs g ax dir ident

      idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
    fromFunc (dims g) $ \idx ->
      case flip List.first (axesBlanks !! (idxMapper idx)) $ \idx2 ->
        if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing of
        Nothing -> Nothing
        Just idx2 -> Just $ Axis.dist DiagDist idx idx2


distToNearestValInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> a -> Axis -> Direction -> Grid (Maybe Int)
distToNearestValInAxDir g x ax dir =
  if not (containsVal x g) then Lib.Grid.const (dims g) Nothing
  else
    let axesVals :: [[Index]] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident ->
          valLineIdxs g x ax dir ident
        idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax in

      fromFunc (dims g) $ \idx ->
        case flip List.first (axesVals !! (idxMapper idx)) $ \idx2 ->
          if Direction.precedes ax dir idx idx2 then Just idx2 else Nothing of
          Nothing -> Nothing
          Just idx2 -> Just $ Axis.dist DiagDist idx idx2


-- TODO: how to make this faster?
extremeDistToPred :: (Unbox a, HasBlank a) => (Index -> Index -> Int) -> (Index -> a -> Bool) -> Grid a -> Grid Int
extremeDistToPred distFunc predF g =
  flip Lib.Grid.map g $ \idx _ ->
    abs (List.maximum (List.map (distFunc idx) gridPredIdxs)) where
    gridPredIdxs = Set.toList $ predIdxs g predF


-- TODO: how to make this faster?
-- FIXME: Could currently include 0s. Do we want this? If not, we have to guard that
-- there are at least 2 non blanks in the grid
extremeDistToNonBlank :: (Unbox a, HasBlank a) => (Index -> Index -> Int) -> Grid a -> Grid Int
extremeDistToNonBlank distFunc g = extremeDistToPred distFunc (\_ val -> nonBlank val) g

extremeDistToBlank :: (Unbox a, HasBlank a) => (Index -> Index -> Int) -> Grid a -> Grid Int
extremeDistToBlank distFunc g = extremeDistToPred distFunc (\_ val -> isBlank val) g

extremeDistToVal :: (Unbox a, Eq a, HasBlank a) => (Index -> Index -> Int) -> Grid a -> a -> Grid Int
extremeDistToVal distFunc g x = extremeDistToPred distFunc (\_ val -> val == x) g


distToNonBlankLineInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid (Maybe Int)
distToNonBlankLineInAxDir g ax dir = runIdentity $ do
  let linesWithNonBlank :: [Int] = flip List.filter (range (Line.numAxLines (dims g) ax)) $ \lineId ->
        flip Prelude.any (Line.idxsOfId (dims g) ax lineId) $ \idx -> nonBlank (getG g idx)
  let orderedNonBlankLines :: [Int] = if dir == Reverse then reverse linesWithNonBlank else linesWithNonBlank
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
  let decider :: Int -> Int -> Bool  = case dir of
        Normal -> \i1 i2 -> i1 > i2
        Reverse -> \i1 i2 -> i1 < i2
  let distPerLine :: [Maybe Int] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \lineId ->
        case flip List.first orderedNonBlankLines (\ident ->
          if decider ident lineId then Just ident else Nothing) of
          Nothing -> Nothing
          Just ident1 -> Just (abs (lineId - ident1))
  pure $ fromFunc (dims g) $ \idx -> (distPerLine !! (idxMapper idx))


nonBlankLineExistsInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid Bool
nonBlankLineExistsInAxDir g ax dir = runIdentity $ do
  let linesWithNonBlank :: [Int] = flip List.filter (range (Line.numAxLines (dims g) ax)) $ \lineId ->
        flip Prelude.any (Line.idxsOfId (dims g) ax lineId) $ \idx -> nonBlank (getG g idx)
  -- ordering is just an optimization in this case
  let orderedNonBlankLines :: [Int] = if dir == Reverse then reverse linesWithNonBlank else linesWithNonBlank
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
  let decider :: Int -> Int -> Bool  = case dir of
        Normal -> \i1 i2 -> i1 > i2
        Reverse -> \i1 i2 -> i1 < i2
  let decisionPerLine :: [Bool] = flip Prelude.map (range (Line.numAxLines (dims g) ax )) $ \lineId ->
        flip Prelude.any orderedNonBlankLines $ \ident -> decider ident lineId
  pure $ fromFunc (dims g) $ \idx -> (decisionPerLine !! (idxMapper idx))


lineWithValExistsInAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> a -> Axis -> Direction -> Grid Bool
lineWithValExistsInAxDir g x ax dir = runIdentity $ do
  let linesWithVal :: [Int] = flip List.filter (range (Line.numAxLines (dims g) ax)) $ \lineId ->
        flip Prelude.any (Line.idxsOfId (dims g) ax lineId) $ \idx -> (getG g idx) == x
  -- ordering is just an optimization in this case
  let orderedLinesWithVal :: [Int] = if dir == Reverse then reverse linesWithVal else linesWithVal
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
  let decider :: Int -> Int -> Bool  = case dir of
        Normal -> \i1 i2 -> i1 > i2
        Reverse -> \i1 i2 -> i1 < i2
  let decisionPerLine :: [Bool] = flip Prelude.map (range (Line.numAxLines (dims g) ax )) $ \lineId ->
        flip Prelude.any orderedLinesWithVal $ \ident -> decider ident lineId
  pure $ fromFunc (dims g) $ \idx -> (decisionPerLine !! (idxMapper idx))



nonBlankExistsToAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> Axis -> Direction -> Grid Bool
nonBlankExistsToAxDir g ax dir = do
  let axesMaxNonBlanks :: [Index] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident -> do
        let lineNonBlankIdxs = flip List.filter (Line.idxsOfId (dims g) ax ident) $ \idx ->
              nonBlank (getG g idx)
        -- (-1, -1) indicates the non-existence of blanks
        if null lineNonBlankIdxs then (Index (-1) (-1)) else Direction.furthestInAxDir lineNonBlankIdxs ax dir
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
  fromFunc (dims g) $ \idx -> do
    let maxInLine :: Index = axesMaxNonBlanks !! (idxMapper idx)
    if maxInLine == Index (-1) (-1) then False else Direction.precedes ax dir idx maxInLine


valExistsToAxDir :: (Unbox a, HasBlank a, Eq a) => Grid a -> a -> Axis -> Direction -> Grid Bool
valExistsToAxDir g x ax dir = do
  let axesMaxVals :: [Index] = flip Prelude.map (range (Line.numAxLines (dims g) ax)) $ \ident -> do
        let lineValIdxs = flip List.filter (Line.idxsOfId (dims g) ax ident) $ \idx ->
              (getG g idx) == x
        -- (-1, -1) indicates the non-existence of a val in axdir
        if null lineValIdxs then (Index (-1) (-1)) else Direction.furthestInAxDir lineValIdxs ax dir
  let idxMapper :: Index -> Int = Line.idxAxisId (dims g) ax
  -- FIXME -- want to avoident !! constant time lookup. Use hashmap for vals?
  fromFunc (dims g) $ \idx -> do
    let maxInLine :: Index = axesMaxVals !! (idxMapper idx)
    if maxInLine == Index (-1) (-1) then False else Direction.precedes ax dir idx maxInLine


----------------------
-- Rects
----------------------

cropDeltas :: Grid a -> Axis -> [Int]
cropDeltas grid ax =
  case ax of
    Horizontal -> List.range $ nCols grid
    Vertical -> List.range $ nRows grid
    _ -> List.range $ min (nRows grid) (nCols grid)

cropAlongAxDirOpt :: Grid a -> Axis -> Direction -> Int -> Maybe Rect
cropAlongAxDirOpt grid ax dir delta =
  case (ax, dir) of
    (Horizontal, Normal) -> do
      guard $ delta < nCols grid
      pure $ Rect (Index 0 delta) (Dims (nRows grid) ((nCols grid) - delta))
    (Horizontal, Reverse) -> do
      guard $ delta < nCols grid
      pure $ Rect (Index 0 0) (Dims (nRows grid) ((nCols grid) - delta))
    (Vertical, Normal) -> do
      guard $ delta < nRows grid
      pure $ Rect (Index delta 0) (Dims ((nRows grid) - delta) (nCols grid))
    (Vertical, Reverse) -> do
      guard $ delta < nRows grid
      pure $ Rect (Index 0 0) (Dims ((nRows grid) - delta) (nCols grid))
    (DownRight, Normal) -> do
      guard $ delta < min (nRows grid) (nCols grid)
      pure $ Rect (Index delta delta) (Dims ((nRows grid) - delta) ((nCols grid) - delta))
    (DownRight, Reverse) -> do
      guard $ delta < min (nRows grid) (nCols grid)
      pure $ Rect (Index 0 0) (Dims ((nRows grid) - delta) ((nCols grid) - delta))
    (DownLeft, Normal) -> do
      guard $ delta < min (nRows grid) (nCols grid)
      pure $ Rect (Index delta 0) (Dims ((nRows grid) - delta) ((nCols grid) - delta))
    (DownLeft, Reverse) -> do
      guard $ delta < min (nRows grid) (nCols grid)
      pure $ Rect (Index 0 delta) (Dims ((nRows grid) - delta) ((nCols grid) - delta))

rectInBounds :: (Unbox a) => Grid a -> Rect -> Bool
rectInBounds g (Rect ul (Dims nR nC)) =
  Dims.inBounds (dims g) (ul + (Index (nR - 1) (nC - 1))) && Dims.inBounds (dims g) ul

nonBlankRect :: (Unbox a, HasBlank a) => Grid a -> Maybe Rect
nonBlankRect g = do
  let (minRow, maxRow, minCol, maxCol) = Dims.iter (dims g) (nRows g, 0, nCols g, 0) $ \vals@(minRow, maxRow, minCol, maxCol) idx@(Index i j) -> pure $
        if nonBlank (getG g idx)
        then (min minRow i, max maxRow i, min minCol j, max maxCol j)
        else vals
  guard $ minRow < nRows g && minCol < nCols g
  pure $ Rect { Rect.upperLeft = Index minRow minCol, Rect.dims = Dims (maxRow + 1 - minRow) (maxCol + 1 - minCol) }

getRect :: (Unbox a) => Grid a -> Rect -> Grid a
getRect g (Rect ul dims) = getSubgridUnsafe g dims ul

embedRectIn :: (Unbox a, HasBlank a) => Grid a -> Rect -> Grid a -> Maybe (Grid a)
embedRectIn bg rect@(Rect (Index ri rj) rDims@(Dims dx dy)) g = do
  let outerDims = dims bg
  guard $ rDims == dims g
  guard $ ri + dx <= Dims.nRows outerDims
  guard $ rj + dy <= Dims.nCols outerDims
  pure $ fromFunc outerDims $ \idx@(Index i j) ->
    if (i >= ri && i < ri + dx && j >= rj && j < rj + dy) then
      getG g (idx - Index ri rj)
    else getG bg idx

embedRectInBlank :: (Unbox a, HasBlank a) => Dims -> Rect -> Grid a -> Maybe (Grid a)
embedRectInBlank outerDims = embedRectIn (Lib.Grid.const outerDims blank)

----------------------
-- Shapes
----------------------

nonBlankShape :: (Unbox a, HasBlank a) => Grid a -> Maybe (Shape a)
nonBlankShape g =
  case nonBlankRect g of
    Just r -> Just $ Shape.fromList (flip Prelude.map (Rect.getIdxs r) (\idx -> (idx, getG g idx)))
    Nothing -> Nothing

-- TODO: slow, but not perf critical and annoying to get destructive updates
fromShapes :: (Unbox a, HasBlank a) => Dims -> [Shape a] -> Grid a
fromShapes dims shapes = fromFunc dims $ \idx ->
  case flip List.first shapes $ \s -> Shape.lookupIndex s idx of
    Nothing -> blank
    Just x -> x

replacingShapes :: (Unbox a, HasBlank a) => Grid a -> [Shape a] -> [Shape a] -> Grid a
replacingShapes g oldShapes newShapes = flip Lib.Grid.map g $ \idx x0 ->
  case flip List.first newShapes $ \s -> Shape.lookupIndex s idx of
    Just x -> x
    Nothing ->
      case flip List.first oldShapes $ \s -> Shape.lookupIndex s idx of
        Just _ -> blank
        Nothing -> x0

lookupShape :: (Unbox a, HasBlank a) => Grid a -> Shape b -> Shape a
lookupShape g s = Shape.fromList $ Prelude.map (\idx -> (idx, getG g idx)) $ Shape.indices s

shapeOrthoNeighbors :: (Unbox a, Eq a, Ord a) => Grid a -> Shape a -> [Index]
shapeOrthoNeighbors g s =
  let allNeighbors = List.nub $ List.iter (Shape.indices s) [] $ \acc sIdx -> pure $ acc ++ (neighborsOrtho g sIdx) in
    List.filter (\neighbIdx -> not (Shape.containsIndex s neighbIdx)) allNeighbors

shapeDiagNeighbors :: (Unbox a, Eq a, Ord a) => Grid a -> Shape a -> [Index]
shapeDiagNeighbors g s =
  let allNeighbors = List.nub $ List.iter (Shape.indices s) [] $ \acc sIdx -> pure $ acc ++ (neighborsDiag g sIdx) in
    List.filter (\neighbIdx -> not (Shape.containsIndex s neighbIdx)) allNeighbors

shapeAllNeighbors :: (Unbox a, Eq a, Ord a) => Grid a -> Shape a -> [Index]
shapeAllNeighbors g s =
  let allNeighbors = List.nub $ List.iter (Shape.indices s) [] $ \acc sIdx -> pure $ acc ++ (neighbors g sIdx) in
    List.filter (\neighbIdx -> not (Shape.containsIndex s neighbIdx)) allNeighbors


shapesNeighbors :: (Unbox a, Eq a, Ord a) => Grid a -> [Shape a] -> (Grid a -> Shape a -> [Index]) -> [Index]
shapesNeighbors g shapes neighborFn = List.nub $ List.iter shapes [] $ \acc s -> pure $ acc ++ (neighborFn g s)
