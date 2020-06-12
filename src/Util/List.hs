-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
module Util.List where

import Util.Imports
import Util.Pre
import qualified Util.Int as Int
import Data.List hiding (partition)
import qualified Data.Set as Set

getUnique :: (Eq b, Ord b) => (a -> b) -> [a] -> Maybe b
getUnique key xs = do
  let uniques = uniq . map key $ xs
  guard $ length uniques == 1
  Just . head $ uniques

-- TODO: arg ord convention
allSame :: (Eq a) => [a] -> Bool
allSame []      = True
allSame (x0:xs) = all (==x0) xs

enumerate :: [a] -> [(Int, a)]
enumerate xs = zip [0..] xs

countDistinct :: (Eq b, Ord b) => (a -> b) -> [a] -> Int
countDistinct key = length . group . map key . sortOn key

allDistinct :: (Eq a, Ord a) => [a] -> Bool
allDistinct xs = length xs == Set.size (Set.fromList xs)

-- TODO: perf
counts :: (Eq a) => [a] -> [Int]
counts xs = map (\x -> count (==x) xs) xs

count :: (a -> Bool) -> [a] -> Int
count p = length . filter p

majority :: (a -> Bool) -> [a] -> Bool
majority p l = (count p l) > majorityCount where
  majorityCount = (length l) `div` 2

first :: (a -> Maybe b) -> [a] -> Maybe b
first f [] = Nothing
first f (x:xs) = case f x of
  Nothing -> Util.List.first f xs
  Just y -> Just y

argmaxKey :: Ord b => (a -> b) -> [a] -> a
argmaxKey key xs = maximumBy (comparing key) xs

argmaxesKey :: Ord b => (a -> b) -> [a] -> [a]
argmaxesKey key xs =
  let keyMax = maximum (map key xs) in
    filter (\x -> key x == keyMax) xs

headO :: [a] -> Maybe a
headO [] = Nothing
headO (x:_) = Just x

argminKey :: Ord b => (a -> b) -> [a] -> a
argminKey key xs = minimumBy (comparing key) xs

argminsKey :: Ord b => (a -> b) -> [a] -> [a]
argminsKey key xs =
  let keyMin = minimum (map key xs) in
    filter (\x -> key x == keyMin) xs

uniq :: (Eq a, Ord a) => [a] -> [a]
uniq = Set.toList . Set.fromList

stableUniqKey :: (Eq b, Ord b) => (a -> b) -> [a] -> [a]
stableUniqKey key xs = go Set.empty xs
  where
    go seen [] = []
    go seen (x:xs) = if Set.member (key x) seen
                     then go seen xs
                     else x:(go (Set.insert (key x) seen) xs)

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f xs = map (uncurry f) (zip (range (length xs)) xs)

range :: Int -> [Int]
range n = [0..(n-1)]

uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f ~(a,b,c) = f a b c

uncurry4 :: (a -> b -> c -> d -> e) -> ((a, b, c, d) -> e)
uncurry4 f ~(a,b,c,d) = f a b c d

iterM :: (Monad m) => [a] -> b -> (b -> a -> m b) -> m b
iterM xs acc f = foldlM' f acc xs

iter :: [a] -> b -> (b -> a -> Identity b) -> b
iter xs acc f = runIdentity $ iterM xs acc f

reduce :: (b -> b -> b) -> (a -> b) -> [a] -> b
reduce op key (x0:xs) = iter xs (key x0) $ \acc x -> pure $ op acc (key x)

indexInSorted :: (Eq a, Ord a) => [a] -> [Int]
indexInSorted xs =
  -- xs:        [5, 1, 2, 8]
  -- positions: [1, 2, 0, 3]
  -- ranks:     [2, 0, 1, 3]
  let positions = map snd . sortOn fst $ zip xs [0..]
      ranks = map snd . sortOn fst $ zip positions [0..] in
    ranks

avg :: [Int] -> Float
avg xs = fromIntegral (sum xs) / fromIntegral (length xs)

flatten :: [[a]] -> ([a], [b] -> [[b]])
flatten xss = (concat xss, unflattenLike xss)

unflattenLike :: [[a]] -> [b] -> [[b]]
unflattenLike [] [] = []
unflattenLike (xs:xss) ys = take (length xs) ys : unflattenLike xss (drop (length xs) ys)

cartesianProduct :: [[a]] -> [[a]]
cartesianProduct [] = [[]]
cartesianProduct (xs:xss) = do
  x <- xs
  rest <- cartesianProduct xss
  pure $ x:rest

split :: Int -> [a] -> [[a]]
split _ [] = []
split n l
  | n > 0 = (take n l) : (Util.List.split n (drop n l))
  | otherwise = error "Negative or zero n"

partitionOn :: [Bool] -> [a] -> ([a], [a])
partitionOn bs xs = (map snd . filter fst $ zip bs xs, map snd . filter (not . fst) $ zip bs xs)

unpartitionOn :: [Bool] -> [b] -> [b] -> [b]
unpartitionOn []         []     []     = []
unpartitionOn (True:bs)  (x:xs) ys     = x : unpartitionOn bs xs ys
unpartitionOn (False:bs) xs     (y:ys) = y : unpartitionOn bs xs ys

mostCommon :: Ord a => [a] -> a
mostCommon = snd . maximum . map (\xs -> (length xs, head xs)) . group . sort

leastCommon :: Ord a => [a] -> a
leastCommon = snd . minimum . map (\xs -> (length xs, head xs)) . group . sort
