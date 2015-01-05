module Tct.Its.Data.Bounds 
  (
  Bounds
  , empty

  , boundOf
  , totalBound

  , insert
  , union
  , update
  , updates

  , isDefined
  , defined
  , nonDefined
  ) where


import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)

import qualified Tct.Core.Common.Pretty as PP
import Tct.Core.Common.SemiRing (bigAdd)

import Tct.Its.Data.Complexity

type Bounds k = M.Map k Complexity


empty :: Bounds k
empty = M.empty

boundOf :: (Ord k, Show k) => Bounds k -> k -> Complexity
boundOf bounds k = error err `fromMaybe` M.lookup k bounds
  where err = "Tct.Its.Data.Bounds.boundOf: key '" ++ show k ++ "' not defined."

totalBound :: Bounds k -> Complexity
totalBound = bigAdd . M.elems


isDefined :: Bounds k -> Bool
isDefined = not . M.foldl' k False
  where k b c = b || c == unknown

nonDefined :: Bounds k -> [k]
nonDefined = M.keys . M.filter (== unknown)

defined :: Bounds k -> [k] 
defined = M.keys . M.filter (/= unknown)

insert :: Ord k => k -> Complexity -> Bounds k -> Bounds k
insert = M.insert


union :: Ord k => Bounds k -> Bounds k -> Bounds k
union = M.union

update :: Ord k => k -> Complexity -> Bounds k -> Bounds k
update r c = M.adjust (minimal c) r

updates :: Ord k => Bounds k -> Bounds k -> Bounds k
updates = M.unionWith minimal

instance PP.Pretty k => PP.Pretty (Bounds k) where
  pretty = ppBounds PP.pretty

ppBounds :: (k -> PP.Doc) -> Bounds k -> PP.Doc
ppBounds ppk bs = PP.table [(PP.AlignLeft, a), (PP.AlignLeft, b)]
  where (a,b) = M.foldrWithKey (\k c (ks,cs) -> (ppk k :ks, PP.pretty c :cs)) ([],[]) bs

