{-# LANGUAGE RecordWildCards #-}
module Tct.Its.Data.Timebounds
  (
  Timebounds
  , initialise

  , TimeboundsMap
  , timeboundsMap

  , tboundOf
  , tcostOf
  , totalBound

  --, insert
  , inserts
  , bridge
  , update
  , updates
  , hasProgress
  , filterRules

  , allDefined
  , defined
  , nonDefined
  ) where


import qualified Data.IntMap.Strict      as IM
import           Data.Maybe              (fromMaybe)

import qualified Tct.Core.Common.Pretty  as PP

import qualified Tct.Common.Polynomial   as P
import           Tct.Common.Ring

import           Tct.Its.Data.Complexity
import           Tct.Its.Data.Types      (RuleId)


type Cost = Int

type TimeboundsMap = IM.IntMap Complexity

data Timebounds = Timebounds
  { tbounds_  :: TimeboundsMap
  , tcosts_   :: IM.IntMap Cost
  , leafcost_ :: Cost } 
  deriving Show

timeboundsMap :: Timebounds -> TimeboundsMap
timeboundsMap = tbounds_

-- | @initialise all starts@ sets the complexity of @all@ to 'Unknown' and the complexity of @starts@ to @1@.
initialise :: [RuleId] -> [RuleId] -> Timebounds
initialise allrules startrules = Timebounds {..}
  where
    tbounds   = IM.fromList (zip allrules (repeat unknown))
    tbounds_  = foldl (\tbounds' i -> IM.insert i one tbounds') tbounds startrules
    tcosts_   = IM.fromList (zip allrules (repeat 1))
    leafcost_ = 0

tboundOf :: Timebounds -> RuleId -> Complexity
tboundOf tb rid = error err `fromMaybe` IM.lookup rid (tbounds_ tb)
  where err = "Tct.Its.Data.Timebounds.tboundOf: key '" ++ show rid ++ "' not defined."

tcostOf :: Timebounds -> RuleId -> Int
tcostOf tb rid = error err `fromMaybe` IM.lookup rid (tcosts_ tb)
  where err = "Tct.Its.Data.Timebounds.tcostsOf: key '" ++ show rid ++ "' not defined."

totalBound :: Timebounds -> Complexity
totalBound Timebounds{..} = bigAdd . (toc leafcost_ :) . IM.elems $ IM.unionWith mul tbounds_ (IM.map toc tcosts_)
  where toc = poly . P.constant


allDefined :: Timebounds -> Bool
allDefined = not . IM.foldl' k False . tbounds_
  where k b c = b || c == unknown

nonDefined :: Timebounds -> [RuleId]
nonDefined = IM.keys . IM.filter (== unknown) . tbounds_

defined :: Timebounds -> [RuleId]
defined = IM.keys . IM.filter (/= unknown) . tbounds_

{-insert :: Complexity -> Timebounds -> Timebounds-}
{-insert c tb = IM.insert c (tbounds_ tb)-}

inserts :: Timebounds -> TimeboundsMap -> Timebounds
inserts tb1 tb2 = tb1{tbounds_ = IM.union tb2 (tbounds_ tb1)}

bridge :: Timebounds -> RuleId -> [(RuleId,RuleId)] -> Timebounds
bridge tb r rs = tb 
  { tbounds_ = foldl (\m (k,b) -> IM.insert k b m) (IM.delete r tbounds) rsbounds
  , tcosts_  = foldl (\m (k,c) -> IM.insert k c m) (IM.delete r tcosts) rscosts }
  where
    tbounds  = tbounds_ tb
    tcosts   = tcosts_ tb

    rbound   = tbounds IM.! r
    rcost    = tcosts IM.! r

    rsbounds = map (\(_,new) -> (new, rbound)) rs
    rscosts  = map (\(old,new) -> (new, tcosts IM.! old + rcost)) rs

update :: RuleId -> Complexity -> Timebounds -> Timebounds
update r c tb = tb{tbounds_ = IM.adjust (minimal c) r (tbounds_ tb)}

updates :: Timebounds -> TimeboundsMap -> Timebounds
updates tb1 tb2 = tb1{tbounds_ = IM.unionWith minimal (tbounds_ tb1) tb2}

hasProgress :: Timebounds -> TimeboundsMap -> Bool
hasProgress tb1 tb2 = any (`elem` IM.keys (IM.filter (/=unknown) tb2)) unknowns
  where unknowns = IM.keys $ IM.filter (== unknown) (tbounds_ tb1)

filterRules :: (RuleId -> Bool) -> Timebounds -> Timebounds
filterRules f tb = tb
  { tbounds_ = IM.filterWithKey (\k _ -> f k) (tbounds_ tb)
  , tcosts_  = IM.filterWithKey (\k _ -> f k) (tcosts_ tb) }

instance PP.Pretty (Timebounds) where
  pretty = ppTimebounds

ppTimebounds :: Timebounds -> PP.Doc
ppTimebounds tb = PP.table [(PP.AlignLeft, a), (PP.AlignLeft, b)]
  where (a,b) = IM.foldrWithKey (\k c (ks,cs) -> (PP.int k :ks, PP.pretty c :cs)) ([],[]) (tbounds_ tb)

