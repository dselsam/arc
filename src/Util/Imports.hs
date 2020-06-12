-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Util.Imports (
  traceM, traceIO, trace,
  MonadIO, liftIO,
  guard, when, unless, whenM, unlessM,
  Identity, runIdentity,
  ExceptT, runExceptT, throwError,
  lift,
  MaybeT(MaybeT), runMaybeT,
  ReaderT, ask, asks, runReaderT, Reader, runReader,
  StateT, get, gets, modify, runStateT, evalStateT,
  (<|>), Alternative,
  isNothing, isJust, fromMaybe,
  for_, foldl', foldlM, foldrM,
  comparing,
  Map,
  Set,
  elemIndex,
  xor, onSndWith,
  Default
  ) where

import Debug.Trace
import Control.Monad (guard, when, unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Extra (whenM, unlessM)
import Control.Monad.ST (runST)
import Control.Applicative ((<|>), empty, Alternative)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT), runMaybeT)
import Control.Monad.Reader (ReaderT, ask, asks, runReaderT, Reader, runReader)
import Control.Monad.State (StateT, get, gets, modify, runStateT, evalStateT)

import Data.Maybe (isNothing, isJust, fromMaybe)
import Data.Foldable (foldl', for_, foldlM, foldrM)
import Data.Ord (comparing)

import Data.Map (Map)
import Data.Set (Set)
import Data.List (elemIndex)

import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Data.Default

xor x y = (x && not y) || (y && not x)

derivingUnbox "Maybe"
    [t| forall a. (Default a, Unbox a) => Maybe a -> (Bool, a) |]
    [| maybe (False, def) (\ x -> (True, x)) |]
    [| \ (b, x) -> if b then Just x else Nothing |]

onSndWith f (x,y) = (x, f y)
