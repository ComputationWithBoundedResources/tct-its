module Tct.Its.Processor.Chaining
  ( chaining
  , chainingCandidates
  , isUnknown
  , maxCost
  , maxOuts
  ) where

import           Control.Monad
import qualified Data.IntMap.Strict           as IM

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds      as TB
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types


data ChainProcessor = ChainProcessor [RuleId]
  deriving Show

data ChainProof
  = ChainProof
    { removedRule :: RuleId
    , addedRules  :: [RuleId] }
  | NoChainProof
  deriving Show

instance PP.Pretty ChainProof where
  pretty NoChainProof
    = PP.text "No rule found for the application."
  pretty pproof = PP.hsep
    [ PP.text "We combine rule"
    , PP.int (removedRule pproof)
    , PP.text "with rules"
    , PP.pretty (addedRules pproof)
    , PP.dot ]

instance Xml.Xml ChainProof where
  toXml NoChainProof = Xml.elt "nochain" []
  toXml _            = Xml.elt "chain" []

instance T.Processor ChainProcessor where
  type ProofObject ChainProcessor = ApplicationProof ChainProof
  type In  ChainProcessor         = Its
  type Out ChainProcessor         = Its
  type Forking ChainProcessor     = T.Optional T.Id

  execute _ prob | isClosed prob = closedProof prob
  execute (ChainProcessor choice) prob =
    case foldl (\acc r -> acc `mplus` chainOne prob r) Nothing choice of
      Nothing              -> progress NoProgress (Applicable NoChainProof)
      Just (nprob, pproof) -> progress (Progress nprob) (Applicable pproof)


chainOne :: Its -> RuleId -> Maybe (Its, ChainProof)
chainOne prob r = do
  let
    succs  = map fst (TG.successors (tgraph_ prob) r)
    irules = irules_ prob
    rrule  = irules IM.! r
  msuccs <- if r `elem` succs then Nothing else Just succs
  nrules <- forM msuccs (chain rrule . (irules IM.!))
  let
    nextid = maximum (IM.keys irules) + 1
    nirules = zip [nextid ..] nrules
    ris = fst (unzip nirules)
    newrules = IM.union (IM.fromList nirules) (IM.delete r irules)
    nprob = prob
      { irules_          = newrules
      , tgraph_          = TG.estimateGraph newrules
      , timebounds_      = TB.bridge (timebounds_ prob) r (zip msuccs ris)
      , localSizebounds_ = Nothing
      , rvgraph_         = Nothing
      , sizebounds_      = Nothing }
  return (nprob, ChainProof r ris)


chaining :: [RuleId] -> ItsStrategy
chaining = T.Apply . ChainProcessor

chainingCandidates :: (Its -> RuleId -> Bool) -> Its -> [RuleId] -> [RuleId]
chainingCandidates f prob = filter (f prob)

isUnknown :: Its -> RuleId -> Bool
isUnknown prob = (`elem` TB.nonDefined (timebounds_ prob))

maxCost :: Int -> Its -> RuleId -> Bool
maxCost n prob r = TB.tcostOf (timebounds_ prob) r <=  n

-- FIXME: we should compute out wrt to the function symbol not the rule
maxOuts :: Int -> Its -> RuleId -> Bool
maxOuts n prob r = null $ drop n (TG.successors (tgraph_ prob) r)

