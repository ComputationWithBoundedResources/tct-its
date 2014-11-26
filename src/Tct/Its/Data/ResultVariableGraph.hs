module Tct.Its.Data.ResultVariableGraph 
  (
  RVGraph
  , initialise  
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
import Tct.Its.Data.Cost (activeVariables)
import Tct.Its.Data.LocalSizebounds


initialise :: TGraph -> LocalSizebounds -> RVGraph
initialise tgraph lbounds = Gr.mkGraph ns es
  where
    rvss = M.keys lbounds
    ns   = zip [0..] rvss
    es   = [ (n1, n2, ()) | (n1,r1) <- ns, (n2,r2) <- ns, k r1 r2 ]

    k (r1,_,v1) rv@(r2,_,_) =
      r1 `elem` Gr.pre tgraph r2
      && v1 `elem` activeVariables (lbounds `lboundOf` rv)

predecessors = undefined

{-toRV :: RVGraph -> Int -> RV-}
{-toRV rvgraph i = fromJust (Gr.lab rvgraph i)-}

incoming :: RVGraph -> [RV] -> [RV]
incoming rvgraph rvs = preds L.\\ rvs
  where 
    rvids   = fst . unzip $ Gr.mkNodes_ (Gr.fromGraph rvgraph) rvs
    predids = L.nub $ concatMap (Gr.pre rvgraph) rvids
    preds = map (fromJust . Gr.lab rvgraph) predids

{-sccs :: RVGraph -> [[RV]]-}
{-sccs = map (map toRV) . Gr.scc-}

