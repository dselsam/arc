-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
module Util.Pre where

foldlM' :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldlM' _ z [] = return z
foldlM' f z (x:xs) = do
  z' <- f z x
  z' `seq` foldlM' f z' xs
