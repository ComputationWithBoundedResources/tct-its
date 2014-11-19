module Tct.Its.Data.ResultVariableGraph 
  (
  RVGraph
  , initialise  
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Graph.Inductive as G

import Tct.Its.Data.Types
import Tct.Its.Data.Cost (activeVariables)
import qualified Tct.Its.Data.LocalSizebounds as LB


initialise :: TGraph -> LB.LocalSizebounds -> RVGraph
initialise tgr lsbs = G.mkGraph ns es
  where
    rvss = M.keys lsbs
    ns = zip [1..] rvss 
    es = [ (n1, n2, ()) | (n1,r1) <- ns, (n2,r2) <- ns, k r1 r2 ]
    k (r1,_,v1) rv@(r2,_,_) =
      r1 `elem` G.pre tgr r2
      && v1 `elem` activeVariables (rv `LB.bound` lsbs)

