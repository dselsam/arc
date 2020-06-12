-- Copyright (c) 2020 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Selsam, Ryan Krueger, Jesse Michael Han.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
module Search.History where

import Control.DeepSeq
import GHC.Generics (Generic, Generic1)
import Util.Imports
import Data.List
import Search.Entry (Entry(Entry))
import qualified Search.Entry as Entry

data Datum = DatumEntry Entry | DatumHistory String History | DatumString String deriving (Eq, Ord, Show, Generic)
instance NFData Datum

isDatumEntry (DatumEntry _) = True
isDatumEntry (DatumHistory _ _) = False

data History = History [Datum] deriving (Eq, Ord, Generic)

instance NFData History

empty :: History
empty = History []

addEntry :: Entry -> History -> History
addEntry e (History ds) = History (DatumEntry e:ds)

addHistory :: String -> History -> History -> History
addHistory n h (History ds) = History (DatumHistory n h:ds)

addString :: String -> History -> History
addString s (History ds) = History (DatumString s:ds)

nOuters :: History -> Int
nOuters (History ds) = length ds

countRec :: (Entry -> Bool) -> History -> Int
countRec p (History ds) = sum (map (countRecData p) ds)

countRecData p (DatumEntry e)     = if p e then 1 else 0
countRecData p (DatumHistory _ h) = countRec p h
countRecData p (DatumString _)    = 0

showCondensed :: History -> String
showCondensed (History ds) = intercalate "," (map showDatumCondensed $ reverse ds)
  where
    showDatumCondensed (DatumEntry (Entry cp c)) = cp ++ ":" ++ c
    showDatumCondensed (DatumHistory _ _) = "<H>"


-- TODO: use pretty-printing library?
showHistory :: Int -> History -> String
showHistory nest (History ds) = showHistoryCore nest (History $ reverse ds)
  where
    showHistoryCore :: Int -> History -> String
    showHistoryCore nest (History ds) = intercalate "\n" $ map (showDatum nest) $ ds

    showDatum nest (DatumEntry e)                = replicate nest ' ' ++ show e
    showDatum nest (DatumHistory t (History ds)) = t ++ ":\n" ++ showHistoryCore (nest+2) (History $ reverse ds)
    showDatum nest (DatumString s)               = replicate nest ' ' ++ s

instance Show History where
  show = showHistory 0
