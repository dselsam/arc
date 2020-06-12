-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}

module Synth.Ex where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Synth.ExInfo
import qualified Data.List as List
import qualified Util.List as List
import Data.Hashable
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

type ForTrain a = [a]
type ForTest a  = [a]

data Ex a = Ex {
  train :: [a],
  test  :: [a]
  } deriving (Eq, Ord, Show, Generic, Generic1)

instance NFData a => NFData (Ex a)

instance Hashable a => Hashable (Ex a) where
  hashWithSalt salt (Ex train test) = hashWithSalt salt (train, test)

-- TODO: better to keep the Ex prefixes everywhere for clarity?
instance Functor Ex where
  fmap f (Ex train test) = Ex (fmap f train) (fmap f test)

instance Foldable Ex where
  foldMap f (Ex train test) = foldMap f train <> foldMap f test

instance Traversable Ex where
  traverse f (Ex train test) = Ex <$> traverse f train <*> traverse f test

getInfo   (Ex train test) = ExInfo (length train) (length test)

toBigList (Ex train test) = train ++ test
fromBigList xs (ExInfo nTrain nTest) = Ex (take nTrain xs) (drop nTrain xs)

replicate (ExInfo nTrain nTest) a = Ex (List.replicate nTrain a) (List.replicate nTest a)

replicateLikeNested :: Ex [a] -> Ex b -> Ex b
replicateLikeNested xss ys = Ex (concatMap (\(xs, y) -> List.replicate (length xs) y) (Prelude.zip (train xss) (train ys)))
                                (concatMap (\(xs, y) -> List.replicate (length xs) y) (Prelude.zip (test xss) (test ys)))

-- Note: all unnecessary, but useful to keep lists-vs-ex straight
map  :: (a -> b) -> Ex a -> Ex b
map f ex = fmap f ex

mapM  :: (Monad m) => (a -> m b) -> Ex a -> m (Ex b)
mapM = Traversable.mapM

all :: (a -> Bool) -> Ex a -> Bool
all = Foldable.all

any :: (a -> Bool) -> Ex a -> Bool
any = Foldable.any

zip     (Ex t1 u1) (Ex t2 u2) = Ex (Prelude.zip t1 t2) (Prelude.zip u1 u2)
zip3    (Ex t1 u1) (Ex t2 u2) (Ex t3 u3) = Ex (Prelude.zip3 t1 t2 t3) (Prelude.zip3 u1 u2 u3)
zip4    (Ex t1 u1) (Ex t2 u2) (Ex t3 u3) (Ex t4 u4) = Ex (List.zip4 t1 t2 t3 t4) (List.zip4 u1 u2 u3 u4)

unzip :: Ex (a, b) -> (Ex a, Ex b)
unzip (Ex xyTrains xyTests) =
  let (xTrains, yTrains) = List.unzip xyTrains
      (xTests,  yTests)  = List.unzip xyTests
  in
    (Ex xTrains xTests, Ex yTrains yTests)

unzip3 :: Ex (a, b, c) -> (Ex a, Ex b, Ex c)
unzip3 (Ex xyzTrains xyzTests) =
  let (xTrains, yTrains, zTrains) = List.unzip3 xyzTrains
      (xTests,  yTests, zTests)  = List.unzip3 xyzTests
  in
    (Ex xTrains xTests, Ex yTrains yTests, Ex zTrains zTests)

unzip4 :: Ex (a, b, c, d) -> (Ex a, Ex b, Ex c, Ex d)
unzip4 (Ex xyzwTrains xyzwTests) =
  let (xTrains, yTrains, zTrains, wTrains) = List.unzip4 xyzwTrains
      (xTests,  yTests, zTests, wTests)  = List.unzip4 xyzwTests
  in
    (Ex xTrains xTests, Ex yTrains yTests, Ex zTrains zTests, Ex wTrains wTests)

sequence :: Ex [a] -> [Ex a]
sequence (Ex trainss testss) =
  [Ex train test | train <- Traversable.sequence trainss, test <- Traversable.sequence testss]

pullList :: Ex [a] -> [Ex a]
pullList (Ex (trains :: [[a]]) (tests :: [[a]])) =
  flip Prelude.map (Prelude.zip trains tests) $ uncurry Ex

pushList :: [Ex a] -> Ex [a]
pushList exs = Ex (Prelude.map train exs) (Prelude.map test exs)

flatten :: Ex [a] -> (Ex a, Ex b -> Ex [b])
flatten xss@(Ex trains tests) = (Ex (concat trains) (concat tests), unflattenLike xss)

unflattenLike :: Ex [a] -> Ex b -> Ex [b]
unflattenLike xss ys = Ex (List.unflattenLike (train xss) $ train ys) (List.unflattenLike (test xss) $ test ys)

flatProvenance :: Ex [a] -> Ex Int
flatProvenance x = Ex (concatMap (\(i, xs) -> List.replicate (length xs) i) (Prelude.zip [0..] (train x)))
                      (concatMap (\(i, xs) -> List.replicate (length xs) (i + length (train x))) (Prelude.zip [0..] (test x)))

partitionOn :: Ex Bool -> Ex a -> (Ex a, Ex a)
partitionOn bs xs =
  let (trainTrues, trainFalses) = List.partitionOn (train bs) (train xs)
      (testTrues,  testFalses)  = List.partitionOn (test bs)  (test xs)
  in
    (Ex trainTrues testTrues, Ex trainFalses testFalses)

unpartitionOn :: Ex Bool -> Ex a -> Ex a -> Ex a
unpartitionOn bs xs ys = Ex (List.unpartitionOn (train bs) (train xs) (train ys))
                            (List.unpartitionOn (test  bs) (test  xs) (test  ys))


{-
TODO: rename these

partitionOn :: Ex [Bool] -> Ex [a] -> (Ex [a], Ex [a])
partitionOn bs xs = Synth.Ex.unzip $ Synth.Ex.map (uncurry List.partitionOn) (Synth.Ex.zip bs xs)

unpartitionOn :: Ex Bool -> Ex a -> Ex a -> Ex a
unpartitionOn b x y = Ex (List.unpartitionOn (train b) (train x) (train y)) (List.unpartitionOn (test b) (test x) (test y))
-}
