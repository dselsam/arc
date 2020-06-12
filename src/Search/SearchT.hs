-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
module Search.SearchT where

import Control.Monad.IO.Class
import Util.Imports
import Debug.Trace
import qualified Control.Monad.Fail as Fail
import Control.Monad.Trans (MonadTrans, lift)
import Control.Applicative (Alternative, empty, (<|>))
import Control.Monad (ap, liftM, when)
import Data.Foldable (for_)
import Search.Entry (Entry(Entry))
import qualified Search.Entry as Entry
import Search.History (History)
import qualified Search.History as History
import Search.Guess (Guess(Guess))
import qualified Search.Guess as Guess
import Search.ScoreFn

type Choice a = (String, a)

data Result a b = Fail
                | Done a
                | Pop Int b
                | WithHistory (History -> b)
                | AddHistory String History b
                | AddString String b -- TODO: awkward but expedient to control nesting
                | ChoicePoint String [Choice b]

data SearchT m a = SearchT (m (Result a (SearchT m a)))

instance (Monad m) => Monad (SearchT m) where
  SearchT f >>= g = SearchT $ do
    result <- f
    case result of
      Fail              -> return $ Fail
      Done x            -> let SearchT y = g x in y
      Pop i k           -> return $ Pop i (k >>= g)
      WithHistory k     -> return $ WithHistory (\h -> k h >>= g)
      AddHistory s h k  -> return $ AddHistory s h (k >>= g)
      AddString s k     -> return $ AddString s (k >>= g)
      ChoicePoint cp cs -> return $ ChoicePoint cp $ map (\(c, k) -> (c, k >>= g)) cs
  return x = SearchT (return $ Done x)
  fail = Fail.fail

instance (Monad m) => Applicative (SearchT m) where
  pure = return
  (<*>) = ap

instance (Monad m) => Functor (SearchT m) where
  fmap = liftM

deadend :: (Monad m) => String -> SearchT m a
deadend _ = SearchT (return Fail)

instance (Monad m) => Fail.MonadFail (SearchT m) where
  fail = deadend

instance MonadTrans SearchT where
  lift f = SearchT (f >>= \x -> return (Done x))

instance (Monad m) => Alternative (SearchT m) where
  empty = deadend "SearchT::Alternative::empty"
  f <|> g = error "why do we need alternative for guard?"

instance (Monad m, MonadIO m) => MonadIO (SearchT m) where
  liftIO a = lift . liftIO $ a

liftO :: (Monad m) => Maybe a -> SearchT m a
liftO Nothing = deadend "liftO failed"
liftO (Just x) = pure x

liftL :: (Monad m, Show a) => [a] -> SearchT m a
liftL xs = oneOf "listL" (map (\x -> (show x, x)) xs)

choice :: (Monad m) => String -> [Choice (SearchT m a)] -> SearchT m a
choice cp cs = SearchT $ pure $ ChoicePoint cp cs

oneOf :: (Monad m) => String -> [Choice a] -> SearchT m a
oneOf cp cs = SearchT $ pure $ ChoicePoint cp $ map (\(c, x) -> (c, pure x)) cs

oneOfS :: (Monad m) => String -> [Choice a] -> SearchT m (String, a)
oneOfS cp cs = SearchT $ pure $ ChoicePoint cp $ map (\(c, x) -> (c, pure (c, x))) cs

oneOfX :: (Monad m) => String -> [Choice a] -> SearchT m (Int, String, a)
oneOfX cp cs = SearchT $ pure $ ChoicePoint cp $ map (\(i, (c, x)) -> (c, pure (i, c, x))) (zip [0..] cs)

pop :: (Monad m) => Int -> SearchT m a -> SearchT m a
pop i psi = SearchT . pure . Pop i $ psi

withHistory :: (Monad m) => (History -> SearchT m a) -> SearchT m a
withHistory psi = SearchT $ pure $ WithHistory psi

addHistory :: (Monad m) => String -> History -> SearchT m a -> SearchT m a
addHistory s h psi = SearchT $ pure $ AddHistory s h psi

addString :: (Monad m) => String -> SearchT m a -> SearchT m a
addString s psi = SearchT $ pure $ AddString s psi
