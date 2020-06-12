-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE StrictData #-}
module Search.ScoreFn where

import Search.History

type ScoreFn m = History -> String -> [(String, Int)] -> m [Int]

defaultScoreFn :: (Monad m) => ScoreFn m
defaultScoreFn entries cp cs = pure $ map snd cs

scoreUptoLevel :: (Monad m) => Int -> ScoreFn m
scoreUptoLevel level entries cp cs = pure $ map (\(_, k) -> if k > level then -1 else k) cs
