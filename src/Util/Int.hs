-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
module Util.Int where

import Util.Imports
import qualified Data.List
import Util.Pre

iterM :: (Monad m) => Int -> b -> (b -> Int -> m b) -> m b
iterM n init f = foldlM' f init [0..(n-1)]

iter :: Int -> b -> (b -> Int -> b) -> b
iter n init f = runIdentity $ iterM n init (\acc k -> pure $ f acc k)

iterFromM :: (Monad m) => Int -> Int -> b -> (b -> Int -> m b) -> m b
iterFromM n k init f = iterM (n - k) init $ \acc n -> f acc (n + k)

iterFrom :: Int -> Int -> b -> (b -> Int -> b) -> b
iterFrom n k init f = runIdentity $ iterFromM n k init (\acc k -> pure $ f acc k)

firstM :: (Monad m) => Int -> (Int -> m (Maybe a)) -> m (Maybe a)
firstM n f = do
  result <- runExceptT $ iterM n () $ \_ i -> do
        o <- lift $ f i
        case o of
          Nothing -> pure ()
          Just x -> throwError x
  case result of
    Left x -> return $ Just x
    Right () -> return Nothing

first :: Int -> (Int -> Maybe a) -> Maybe a
first n f = runIdentity $ firstM n (pure . f)

all :: Int -> (Int -> Bool) -> Bool
all n p = isNothing $ first n $ \k -> if not (p k) then Just () else Nothing

any :: Int -> (Int -> Bool) -> Bool
any n p = isJust $ first n $ \k -> if p k then Just () else Nothing

allSame :: (Eq a) => Int -> (Int -> a) -> Bool
allSame 0 key = True
allSame n key = Util.Int.all n (\k -> key k == key 0)

-- 6, 8, 10
-- 2 is a common divisor
-- We consider n to be a divisor of itself

divisors :: Int -> [Int]
divisors n = [x | x <- [1..n], n `rem` x == 0]

allCommonDivisors :: [Int] -> [Int]
allCommonDivisors []     = []
allCommonDivisors (k0:ks) = foldl' (\acc k -> Data.List.intersect acc (divisors k)) (divisors k0) ks
