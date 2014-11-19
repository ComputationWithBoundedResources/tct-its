module Tct.Its.Data.TransitionGraph 
  (
  TGraph
  , estimateGraph 
  ) where


import qualified Data.Graph.Inductive as G

import Tct.Its.Data.Types
import Tct.Its.Data.Rule


estimateGraph :: Rules -> TGraph
estimateGraph = estimateGraphWith functionSymbols

estimateGraphWith :: (Rule -> Rule -> Bool) -> Rules -> TGraph
estimateGraphWith f rs = G.mkUGraph (indices rs) es
  where es = [ (n1, n2) | (n1,r1) <- rs, (n2,r2) <- rs, f r1 r2 ]

-- | only compares function symbols
functionSymbols :: Rule -> Rule -> Bool
functionSymbols r1 r2 = or [ fun r == lfun | let lfun = fun (lhs r2), r <- rhs r1 ]

