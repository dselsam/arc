-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
module Util.Stack where

data Stack a = Stack {
  size :: Int,
  elems :: [a]
  } deriving (Eq, Ord, Show)

empty :: Stack a
empty = Stack 0 []

pop :: Stack a -> Maybe (a, Stack a)
pop (Stack 0 [])     = Nothing
pop (Stack n (x:xs)) = Just (x, Stack (n-1) xs)

push :: a -> Stack a -> Stack a
push x (Stack n xs) = Stack (n+1) (x:xs)

popMany :: Int -> Stack a -> Stack a
popMany k (Stack n xs)
  | k >= n = empty
  | otherwise = Stack (n-k) (drop k xs)
