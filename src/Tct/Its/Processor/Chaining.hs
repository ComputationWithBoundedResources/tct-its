module Tct.Its.Processor.Chaining 
  ( chaining
  , chainingCandidates
  ) where

import Control.Monad
import qualified Data.IntMap.Strict           as IM

import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds      as TB
import           Tct.Its.Data.ResultVariableGraph (nextSCC)
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types


data ChainProcessor = ChainProcessor [RuleId]
  deriving Show

data ChainProof 
  = ChainProof
    { removedRule :: RuleId 
    , addedRules :: [RuleId] }
  | NoChainProof
  deriving Show

instance PP.Pretty ChainProof where
  pretty NoChainProof
    = PP.text "No rule found for the application."
  pretty pproof = PP.hcat 
    [ PP.text "We combine rule" 
    , PP.int (removedRule pproof) 
    , PP.text "with rules" 
    , PP.pretty (addedRules pproof) 
    , PP.dot ]

instance T.Processor ChainProcessor where
  type ProofObject ChainProcessor = ApplicationProof ChainProof
  type Problem ChainProcessor     = Its

  solve p prob | isClosed prob = return $ closedProof p prob
  solve p@(ChainProcessor choice) prob = 
    case foldl (\acc r -> acc `mplus` chainOne prob r) Nothing choice of 
      Nothing -> return $ progress p prob NoProgress (Applicable NoChainProof)
      Just (nprob, pproof) -> return $ progress p prob (Progress nprob) (Applicable pproof)
    where


chainOne :: Its -> RuleId -> Maybe (Its, ChainProof)
chainOne prob r = do
  let
    succs  = map fst (TG.successors (_tgraph prob) r)
    irules = _irules prob
    rrule  = irules IM.! r
  msuccs <- if r `elem` succs then Nothing else Just succs
  nrules <- forM msuccs (chain rrule . (irules IM.!))
  let 
    nextid = maximum (IM.keys irules) + 1
    nirules = zip [nextid ..] nrules
    ris = fst (unzip nirules)
    nprob = prob
      { _irules          = IM.union (IM.fromList nirules) (IM.delete r irules)
      , _tgraph          = TG.bridge (_tgraph prob) r ris
      , _timebounds      = TB.bridge (_timebounds prob) r (zip msuccs ris)
      , _localSizebounds = Nothing
      , _rvgraph         = Nothing
      , _sizebounds      = Nothing }
  return (nprob, ChainProof r ris)


chaining :: [RuleId] -> T.Strategy Its
chaining = T.Proc . ChainProcessor

chainingCandidates :: Its -> [RuleId]
chainingCandidates prob = case _rvgraph prob  of
  Just rvgraph -> maxOuts $ maxCost $ nextSCC rvgraph tbounds
  _            -> []
  where 
    tbounds = _timebounds prob
    maxCost = filter (\r -> TB.tcostOf tbounds r < 5)
    maxOuts = filter (\r -> length (TG.successors (_tgraph prob) r) < 3)



