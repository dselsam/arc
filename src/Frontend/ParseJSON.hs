-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE TemplateHaskell #-}
module Frontend.ParseJSON where

import qualified Data.ByteString.Lazy as B
import Control.Exception
import Data.Aeson
import Data.Aeson.TH

import Lib.Grid (Grid)
import qualified Lib.Grid as Grid
import Lib.Color (Color(Color))
import qualified Lib.Color as Color
import Synth.Ex (Ex(..))

data Example = Example {
  input :: [[Int]],
  output :: [[Int]]
  } deriving (Show)

data Problem = Problem {
  train :: [Example],
  test  :: [Example]
  } deriving (Show)

concat <$> mapM (deriveJSON defaultOptions) [''Example, ''Problem]

problem2ex :: Problem -> (Ex (Grid Color), Ex (Grid Color))
problem2ex (Problem train test) =
  (Ex (map (Grid.map (\_ -> Color) . Grid.fromLists . input) train) (map (Grid.map (\_ -> Color) . Grid.fromLists . input) test),
   Ex (map (Grid.map (\_ -> Color) . Grid.fromLists . output) train) (map (Grid.map (\_ -> Color) . Grid.fromLists . output) test))

parseExample :: FilePath -> IO (Ex (Grid Color), Ex (Grid Color))
parseExample filepath = do
  bytes <- B.readFile filepath
  case eitherDecode bytes of
    Left err -> throw $ userError err
    Right problem -> return $ problem2ex problem
