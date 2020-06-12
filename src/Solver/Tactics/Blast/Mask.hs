-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}

module Solver.Tactics.Blast.Mask where

import GHC.Generics (Generic, Generic1)
import Control.DeepSeq
import Debug.Trace
import Util.Imports
import qualified Util.List as List
import Util.List (uncurry4)
import Data.List hiding (partition)
import qualified Data.Map as Map
import Synth1.Basic
import Synth.Ex (Ex(..), ForTrain, ForTest)
import qualified Synth.Ex as Ex
import Data.Foldable
import Data.Ratio
import Solver.Tactics.Blast.Goal (Goal(..))
import qualified Solver.Tactics.Blast.Goal as BlastGoal -- note the naming
import qualified Solver.Goal as SolverGoal -- note the naming
import Lib.Grid (Grid)
import Lib.Color (Color)
import qualified Lib.Grid as Grid
import qualified Lib.Dims as Dims
import Search.History
import Data.Hashable
import qualified Data.HashTable.IO as H
import Solver.SolveM
import qualified Search.Guess as Guess


data Mask = Mask {
  masks :: Ex (Grid Bool),
  prior :: PriorFeatures,
  history :: History
  } deriving (Eq, Ord, Show, Generic)

instance NFData Mask

type HashTable k v = H.CuckooHashTable k v

newtype MaskGrid = MaskGrid { maskGridMask :: Mask }

instance Eq MaskGrid where
  MaskGrid (Mask masks1 _ _) == MaskGrid (Mask masks2 _ _) = masks1 == masks2

instance Hashable MaskGrid where
  hashWithSalt salt (MaskGrid (Mask masks _ _)) = hashWithSalt salt masks

uniqMasks :: [Mask] -> IO [Mask]
uniqMasks masks = do
  ht :: HashTable MaskGrid () <- H.new
  -- Must traverse in order
  for_ masks $ \mask -> do
    let maskGrid :: MaskGrid = MaskGrid mask
    lookup <- H.lookup ht maskGrid
    case lookup of
      Nothing -> H.insert ht maskGrid ()
      Just _ -> pure ()
  map (maskGridMask . fst) <$> H.toList ht


computeMasksFn :: (SolverGoal.StdGoal -> Synth1M (Ex (Grid Bool))) -> SolverGoal.StdGoal -> SolveM [Mask]
computeMasksFn synthMasksFn goal = do
  guesses <- liftIO $ runSynth1All (SolverGoal.synthCtx goal) (synthMasksFn goal)
  pure $ flip map (zip [1..] guesses) $ \(rank, Guess.Guess masks history _ _) ->
    let level = 0 -- TODO(ryan): rank, possibly by searching the history for a "bad" string
        prior = PriorFeatures { rank = rank, level = level }
    in
      Mask { masks = masks, prior = prior, history = history }


data PriorFeatures = PriorFeatures {
  rank  :: Int,
  level :: Int
  } deriving (Eq, Ord, Show, Generic)

instance NFData PriorFeatures

data PosteriorFeatures = PosteriorFeatures {
  nInputsWithNewCommitment       :: Int,
  nInputsTotal                   :: Int,
  nTotalCommitments              :: Int,
  nNewCommitments                :: Int,
  nNewCommitmentsSame            :: Int,
  nNewCommitmentsDiff            :: Int
  } deriving (Eq, Ord, Show, Generic)

instance NFData PosteriorFeatures

type Features = (PriorFeatures, PosteriorFeatures)
type RankingFn = Features -> Features -> Ordering

-- TODO: parse flags and store them in the global context
defaultRankingFn :: Features -> Features -> Ordering
defaultRankingFn = comparing $ \(prior, posterior) -> (

  -- should always be first
  - nInputsWithNewCommitment posterior,

  -- swap the below two to get different behavior
  -- so far, swapping level prior and nNewCommitments is all we need. Nested search over them?
  - nNewCommitments posterior,
  level prior,

  - nTotalCommitments posterior,
  - nNewCommitmentsDiff posterior,
  rank prior)

computePosteriorFeatures :: Goal -> Mask -> PosteriorFeatures
computePosteriorFeatures (Goal inputs outputs reconstructs) (Mask masks _ history) = runIdentity $ do
  --let newCommitmentsTT    = Ex.flatten $ Ex.map (uncurry computeCommitmentsTT) (Ex.zip reconstructs masks)
  let newCommitmentsTT    = map (uncurry computeCommitmentsTT) (zip (Ex.train reconstructs) (Ex.train masks))
  let newCommitmentsT     = map (uncurry4 computeCommitmentsT) (zip4 (Ex.train inputs) outputs (Ex.train reconstructs) (Ex.train masks))
  let features = PosteriorFeatures {
    nInputsTotal             = length newCommitmentsTT,
    nTotalCommitments        = sum . map fst $ newCommitmentsTT,
    nNewCommitments          = sum . map snd $ newCommitmentsTT,
    nInputsWithNewCommitment = length . filter ((>0) . snd) $ newCommitmentsTT,
    nNewCommitmentsSame      = sum . map fst $ newCommitmentsT,
    nNewCommitmentsDiff      = sum . map snd $ newCommitmentsT
    }
  pure features

  where
    computeCommitmentsTT :: Grid (Maybe Color) -> Grid Bool -> (Int, Int)
    computeCommitmentsTT reconstruct mask = Dims.iter (Grid.dims reconstruct) (0, 0) $ \(nTotal, nNew) idx -> do
      let r = isJust $ Grid.get reconstruct idx
      let m = Grid.get mask idx
      pure (nTotal + if m then 1 else 0, nNew + if m && not r then 1 else 0)

    computeCommitmentsT :: Grid Color -> Grid Color -> Grid (Maybe Color) -> Grid Bool -> (Int, Int)
    computeCommitmentsT input output reconstruct mask = Dims.iter (Grid.dims input) (0, 0) $ \(nSame, nDiff) idx -> do
      let x = Grid.get input idx
      let y = Grid.get output idx
      let r = isJust $ Grid.get reconstruct idx -- we are currently explaining idx with reconstruct
      let m = Grid.get mask idx -- the mask is true on idx
      let b = m && not r -- the mask is true on idx, and we are NOT currently explaining it
      pure (nSame + if b && x == y then 1 else 0, nDiff + if b && x /= y then 1 else 0)
