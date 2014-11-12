module Tct.Its.Data.Bounds where

import qualified Data.Map.Strict as M


import qualified Tct.Core.Common.Pretty as PP
import Tct.Core.Common.SemiRing (bigAdd)

import Tct.Its.Data.Cost

type Bounds k = M.Map k Cost

isDefined :: Bounds k -> Bool
isDefined = not . M.foldl' k False
  where k b c = b || c == omega

strict :: Bounds k -> [k]
strict = M.keys . M.filter (== omega)

weak :: Bounds k -> [k] 
weak = M.keys . M.filter (/= omega)

union :: Ord k => Bounds k -> Bounds k -> Bounds k
union = M.unionWith minimal

update :: Ord k => k -> Cost -> Bounds k -> Bounds k
update r c = M.adjust (minimal c) r

cost :: Bounds k -> Cost
cost = bigAdd . M.elems

ppBounds :: (k -> PP.Doc) -> Bounds k -> PP.Doc
ppBounds ppk bs = PP.table [(PP.AlignLeft, a), (PP.AlignLeft, b)]
  where (a,b) = M.foldrWithKey (\k c (ks,cs) -> (ppk k :ks, PP.pretty c :cs)) ([],[]) bs

