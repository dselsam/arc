-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Solver.Synth1Context where

import Synth.Ex (Ex)
import qualified Synth.Ex as Ex
import Lib.Color
import Lib.Index
import Lib.Shape (Shape)
import Search.SearchT
import Synth.ExInfo
import Synth.EagerFeatures
import Data.List
import qualified Util.List as List

data Synth1Context = Synth1Context {
  ctxNumTrain    :: Int,
  ctxNumTest     :: Int,
  ctxHaveFocused :: Bool,
  ctxInts        :: [Choice (Ex Int)],
  ctxColors      :: [Choice (Ex Color)],
  ctxIdxs        :: [Choice (Ex Index)],
  ctxIdxLists    :: [Choice (Ex [Index])],
  ctxShapes      :: [Choice (Ex (Shape Color))],
  ctxShapeLists  :: [Choice (Ex ([Shape Color]))]
  } deriving (Eq, Ord, Show)

emptySynth1Context :: Int -> Int -> Synth1Context
emptySynth1Context numTrain numTest = Synth1Context numTrain numTest False [] [] [] [] [] []

removeDuplicateChoicesByName :: [Choice a] -> [Choice a]
removeDuplicateChoicesByName choices = nubBy (\c1 c2 -> fst c1 == fst c2) choices

mergeSynth1Contexts :: Synth1Context -> Synth1Context -> Synth1Context
mergeSynth1Contexts ctx1 ctx2 =
  -- note this check
  if not (ctxNumTrain ctx1 == ctxNumTrain ctx2 && ctxNumTest ctx1 == ctxNumTest ctx2) then ctx1
  else
    -- note how we are using choice point name as equality check!!
    Synth1Context (ctxNumTrain ctx1) (ctxNumTest ctx1) (ctxHaveFocused ctx1 || ctxHaveFocused ctx2)
      (removeDuplicateChoicesByName (ctxInts ctx1 ++ ctxInts ctx2)) -- ctxInts
      (removeDuplicateChoicesByName (ctxColors ctx1 ++ ctxColors ctx2)) -- ctxColors
      (removeDuplicateChoicesByName (ctxIdxs ctx1 ++ ctxIdxs ctx2)) -- ctxIdxs
      (removeDuplicateChoicesByName (ctxIdxLists ctx1 ++ ctxIdxLists ctx2)) -- ctxIdxLists
      (removeDuplicateChoicesByName (ctxShapes ctx1 ++ ctxShapes ctx2)) -- ctxShapes
      (removeDuplicateChoicesByName (ctxShapeLists ctx1 ++ ctxShapeLists ctx2)) -- ctxShapeLists

mergeAllSynth1Contexts :: [Synth1Context] -> Synth1Context
mergeAllSynth1Contexts ctxs =
  if null ctxs then error "null list passed to mergeSynth1Contexts"
  else if not ((List.allSame (map (\ctx -> ctxNumTrain ctx) ctxs)) &&
               (List.allSame (map (\ctx -> ctxNumTest ctx) ctxs))) then (ctxs !! 0)
  else
    Synth1Context (ctxNumTrain (ctxs !! 0)) (ctxNumTest (ctxs !! 0)) (any ctxHaveFocused ctxs)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxInts ctx)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxColors ctx)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxIdxs ctx)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxIdxLists ctx)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxShapes ctx)
      (removeDuplicateChoicesByName $ List.iter ctxs [] $ \acc ctx -> pure $ acc ++ ctxShapeLists ctx)
