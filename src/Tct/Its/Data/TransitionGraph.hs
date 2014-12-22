module Tct.Its.Data.TransitionGraph 
  (
  TGraph
  -- * Construction
  , estimateGraph 
  -- * Queries
  , initialRules 
  , predecessors
  , incoming
  , sccs
  , trivialSCCs
  ) where


import qualified Data.Set as S
import qualified Data.Graph.Inductive as Gr

import qualified Tct.Core.Common.Pretty as PP

import Tct.Its.Data.Types

import Debug.Trace

-- | Transition (or Control-Flow) graph:
--    * Nodes correspond to indices of rules.
--    * There is an edge between two nodes if there exists an evaluation st the latter rule follows the former rule.
--    * Edges are labelled with the corresponding position of the compound symbol.
type TGraph  = Gr.Gr () ComId



-- | Default estimation. See 'functionSymbols'.
estimateGraph :: Rules -> TGraph
estimateGraph = estimateGraphWith functionSymbols

estimateGraphWith :: (Rule -> Rule -> [Int])  -> Rules -> TGraph
estimateGraphWith f irs = Gr.mkGraph ns es
  where 
    ns = map (fmap (const ())) irs
    es  = [ (n1, n2, cid) | (n1,r1) <- irs, (n2,r2) <- irs, cid <- traceShow (n1,n2, f r1 r2) (f r1 r2) ]

-- | Only compares the function symbol.
functionSymbols :: Rule -> Rule -> [ComId]
functionSymbols r1 r2 = [ cid | (cid,r) <- zip [0..] (rhs r1), fun r == fun (lhs r2) ]

-- | Returns all nodes without predecessors.
initialRules :: TGraph -> [RuleId]
initialRules tgraph = filter (\n -> Gr.indeg tgraph n == 0) (Gr.nodes tgraph)

predecessors :: TGraph -> RuleId -> [RV']
predecessors = Gr.lpre

sccs :: TGraph -> [[RuleId]]
sccs = Gr.scc

trivialSCCs :: TGraph -> [RuleId]
trivialSCCs tgraph = concat . filter acyclic  $ Gr.scc tgraph
  where 
    acyclic [scc] = scc `notElem` Gr.suc tgraph scc
    acyclic _     = False

instance PP.Pretty TGraph where
  pretty = PP.pretty . lines . Gr.prettify

incoming :: TGraph -> [RuleId] -> [RV']
incoming tgraph somerules = S.toList $ S.filter ((`S.notMember` ous) . fst) ins
  where 
    ins = S.unions $ map (S.fromList . Gr.lpre tgraph) somerules
    ous = S.fromList somerules

