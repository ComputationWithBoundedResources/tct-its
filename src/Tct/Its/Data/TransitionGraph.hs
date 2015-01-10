module Tct.Its.Data.TransitionGraph 
  (
  TGraph
  -- * Construction
  , estimateGraph 
  -- * Queries
  {-, initialRules -}
  , predecessors
  , successors
  , incoming
  , sccs
  , nextSCC
  , upToNextSCC
  , fromNextSCC
  , trivialSCCs
  ) where


import Control.Monad (void)
import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.Graph.Inductive as Gr

import qualified Tct.Core.Common.Pretty as PP

import Tct.Its.Data.Types
import qualified Tct.Its.Data.Timebounds as TB

-- | Transition (or Control-Flow) graph:
--    * Nodes correspond to indices of rules.
--    * There is an edge between two nodes if there exists an evaluation st the latter rule follows the former rule.
--    * Edges are labelled with the corresponding position of the compound symbol.
type TGraph  = Gr.Gr () ComId



-- | Default estimation. See 'functionSymbols'.
estimateGraph :: Rules -> TGraph
estimateGraph = estimateGraphWith functionSymbols

estimateGraphWith :: (Rule -> Rule -> [Int])  -> Rules -> TGraph
estimateGraphWith f rules = Gr.mkGraph ns es
  where 
    irs = IM.toList rules
    ns  = map void irs
    es  = [ (n1, n2, cid) | (n1,r1) <- irs, (n2,r2) <- irs, cid <- f r1 r2 ]

-- | Only compares the function symbol.
functionSymbols :: Rule -> Rule -> [ComId]
functionSymbols r1 r2 = [ cid | (cid,r) <- zip [0..] (rhs r1), fun r == fun (lhs r2) ]

-- | Returns all nodes without predecessors.
{-initialRules :: TGraph -> [RuleId]-}
{-initialRules tgraph = filter (\n -> Gr.indeg tgraph n == 0) (Gr.nodes tgraph)-}

predecessors :: TGraph -> RuleId -> [RV']
predecessors = Gr.lpre

successors :: TGraph -> RuleId -> [RV']
successors = Gr.lsuc

sccs :: TGraph -> [[RuleId]]
sccs = Gr.scc

trivialSCCs :: TGraph -> [RuleId]
trivialSCCs tgraph = concat . filter acyclic  $ Gr.scc tgraph
  where 
    acyclic [scc] = scc `notElem` Gr.suc tgraph scc
    acyclic _     = False

-- | Returns nextSCC with an open rule.
nextSCC :: TGraph -> TB.Timebounds -> [RuleId]
nextSCC tgraph tbounds = go (sccs tgraph)
  where 
    undefineds = TB.nonDefined tbounds
    go [] = []
    go (scc :ss)
      | any (`elem` undefineds) scc = scc
      | otherwise                   = go ss
      --
-- | Returns nextSCC with an open rule.
upToNextSCC :: TGraph -> TB.Timebounds -> [[RuleId]]
upToNextSCC tgraph tbounds = go (sccs tgraph)
  where 
    undefineds = TB.nonDefined tbounds
    go [] = []
    go (scc :ss)
      | any (`elem` undefineds) scc = [scc]
      | otherwise                   = scc : go ss

-- | Returns all SCCs with an oppen rule.
fromNextSCC :: TGraph -> TB.Timebounds -> [[RuleId]]
fromNextSCC tgraph tbounds = k (sccs tgraph)
  where 
    undefineds = TB.nonDefined tbounds
    k = filter (any (`elem` undefineds))

instance PP.Pretty TGraph where
  pretty = PP.pretty . lines . Gr.prettify

incoming :: TGraph -> [RuleId] -> [RV']
incoming tgraph somerules = S.toList $ S.filter ((`S.notMember` ous) . fst) ins
  where 
    ins = S.unions $ map (S.fromList . Gr.lpre tgraph) somerules
    ous = S.fromList somerules

