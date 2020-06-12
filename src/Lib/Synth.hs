-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Lib.Synth where

import Debug.Trace
import Util.Imports
import qualified Util.Int as Int
import Lib.Blank
import Data.Maybe (isJust)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Synth.Spec (Spec, SynthFn, SynthFn1)
import qualified Synth.Spec as Spec
import Data.Monoid (mempty)
import Data.Set (Set)
import qualified Data.Set as Set
import Synth.EagerFeatures
import Synth.LazyFeatures
import qualified Synth.LazyFeatures as LazyFeatures
import Data.Map (Map)
import qualified Data.Map as Map
import Util.List (uncurry3)
import qualified Util.Int as Int
import qualified Util.List as List
import qualified Data.List as List
import qualified Lib.Dims as Dims
import Lib.Dims (Dims (Dims))
import Synth.Context
import qualified Lib.Index as Index
import Lib.Index (Index (Index))
import Synth.Ex (Ex(..))
import qualified Synth.Ex as Ex
import Lib.Color
import Lib.Blank (HasBlank(..), blank, isBlank, nonBlank)
import qualified Lib.Blank as Blank
import qualified Lib.Rect as Rect
import Lib.Rect (Rect(Rect))
import Lib.Axis
import Synth1.Basic
import Search.SearchT
import Lib.Grid (Grid)
import Lib.Tile (TileData(TileData))
import qualified Lib.Tile as Tile
import qualified Lib.Tile as TileData
import qualified Lib.Grid as Grid
import qualified Lib.Symmetry as Symmetry
import Search.DFS
import Synth.Ints2Int (synthInts2IntE)
import Synth.Spec.ESpec (ESpec(ESpec))
import qualified Synth.Spec.ESpec as ESpec
----------------------------------
-- Ints2<thing-composed-of-ints>
----------------------------------

synthInts2Index :: (Monad m) => SynthFn m ESpec (EagerFeatures Int) Index
synthInts2Index spec@(ESpec info ctx labels) = do
  rows :: Ex Int <- find1 "row" $ synthInts2IntE $ spec { ESpec.labels = map Index.row labels }
  cols :: Ex Int <- find1 "col" $ synthInts2IntE $ spec { ESpec.labels = map Index.col labels }
  pure $ Ex.map (uncurry Index) (Ex.zip rows cols)

synthInts2Dims :: (Monad m) => SynthFn m ESpec (EagerFeatures Int) Dims
synthInts2Dims spec@(ESpec info ctx labels) = do
  rows :: Ex Int <- find1 "nRows" $ synthInts2IntE $ spec { ESpec.labels = map Dims.nRows labels }
  cols :: Ex Int <- find1 "nCols" $ synthInts2IntE $ spec { ESpec.labels = map Dims.nCols labels }
  pure $ Ex.map (uncurry Dims) (Ex.zip rows cols)

synthInts2Rect :: (Monad m) => SynthFn m ESpec (EagerFeatures Int) Rect
synthInts2Rect spec@(ESpec info ctx labels) = do
  idxs :: Ex Index <- find1 "upperLeft" $ synthInts2Index $ spec { ESpec.labels = map Rect.upperLeft labels }
  dims :: Ex Dims  <- find1 "dims" $ synthInts2Dims  $ spec { ESpec.labels = map Rect.dims      labels }
  pure $ Ex.map (uncurry Rect) (Ex.zip idxs dims)

synthInts2TileData :: (Monad m) => SynthFn m ESpec (EagerFeatures Int) TileData
synthInts2TileData spec@(ESpec info ctx labels) = do
  dims  :: Ex Dims <- find1 "dims" $ synthInts2Dims $ spec { ESpec.labels = map TileData.dims labels }
  delta :: Ex Int  <- find1 "delta" $ synthInts2IntE $ spec { ESpec.labels = map TileData.delta labels }
  pure $ Ex.map (uncurry TileData) (Ex.zip dims delta)
