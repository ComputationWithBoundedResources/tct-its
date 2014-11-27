module Tct.Its.Data.ResultVariableGraph 
  (
  RVGraph
  , compute  
  , predecessors
  , incoming
  ) where

import Data.Maybe (fromJust)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Graph.Inductive as Gr
import qualified Data.Graph.Inductive.Query as Gr
import qualified Data.Graph.Inductive.NodeMap as Gr

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

    k (r1,_,v1) rv@(r2,_,_) =
      r1 `elem` Gr.pre tgraph r2
      && v1 `elem` activeVariables (lbounds `lboundOf` rv)

predecessors = undefined

incoming :: RVGraph -> [RV] -> [RV]
incoming rvgraph rvs = preds L.\\ rvs
  where 
    rvids   = fst . unzip $ Gr.mkNodes_ (Gr.fromGraph rvgraph) rvs
    predids = L.nub $ concatMap (Gr.pre rvgraph) rvids
    preds = map (fromJust . Gr.lab rvgraph) predids

