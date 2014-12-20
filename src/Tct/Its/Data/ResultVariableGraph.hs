module Tct.Its.Data.ResultVariableGraph 
  (
  RVGraph
  , compute  
  , predecessors
  , incoming
  , sccs
  , SCC (..)
  ) where

import Data.Maybe (fromJust)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Graph.Inductive as Gr

import Tct.Its.Data.Types
import Tct.Its.Data.TransitionGraph (TGraph)
import Tct.Its.Data.Cost (Cost, Growth, activeVariables)
import Tct.Its.Data.LocalSizebounds (LocalSizebounds, lboundOf, lgrowthOf)

type RVGraph = Gr.Gr RV (Cost,Growth)


compute :: TGraph -> LocalSizebounds -> RVGraph
compute tgraph lbounds = Gr.mkGraph ns es
  where
    rvss = M.keys lbounds
    ns   = zip [0..] rvss
    es   = [ (n1, n2, (lbounds `lboundOf` rv2, lbounds `lgrowthOf` rv2)) | (n1,rv1) <- ns, (n2,rv2) <- ns, k rv1 rv2 ]

    k rv1 rv2 =
      rvRule rv1 `elem` Gr.pre tgraph (rvRule rv2)
      && rvVar rv1 `elem` activeVariables (lbounds `lboundOf` rv2)

predecessors :: RVGraph -> RV -> [RV]
predecessors rvgraph rv = preds
  where
    rvid    = fst $ Gr.mkNode_ (Gr.fromGraph rvgraph) rv
    predids = (Gr.pre rvgraph) rvid
    preds = map (fromJust . Gr.lab rvgraph) predids

incoming :: RVGraph -> [RV] -> [RV]
incoming rvgraph rvs = preds L.\\ rvs
  where 
    rvids   = fst . unzip $ Gr.mkNodes_ (Gr.fromGraph rvgraph) rvs
    predids = L.nub $ concatMap (Gr.pre rvgraph) rvids
    preds = map (fromJust . Gr.lab rvgraph) predids


data SCC a = Trivial a | NonTrivial [a]

instance Functor SCC where
  f `fmap` Trivial a     = Trivial (f a)
  f `fmap` NonTrivial as = NonTrivial (map f as)

-- TODO: check if in topological order
sccs :: RVGraph -> [SCC RV]
sccs rvgraph = map (fmap (fromJust . Gr.lab rvgraph) . isTrivial) (Gr.scc rvgraph)
  where 
    isTrivial [s] 
      | s `elem` Gr.suc rvgraph s = NonTrivial [s]
      | otherwise                 = Trivial s
    isTrivial scc = NonTrivial scc
