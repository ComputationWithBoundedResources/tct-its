module Tct.Its.Data.Graph 
  (
  Graph
  , estimateGraph 
  ) where


import qualified Data.Graph.Inductive as G

import Tct.Its.Data.Rule


type Graph = G.Gr Rule ()

estimateGraph :: [Rule] -> Graph
estimateGraph = estimateGraphWith functionSymbols

estimateGraphWith :: (Rule -> Rule -> Bool) -> [Rule] -> Graph
estimateGraphWith f rs = G.mkGraph ns es
  where
    ns = zip [1..] rs
    es = [ (n1, n2, ()) | (n1,r1) <- ns, (n2,r2) <- ns, f r1 r2 ]

-- | only compares function symbols
functionSymbols :: Rule -> Rule -> Bool
functionSymbols r1 r2 = or [ loc r == lloc | let lloc = loc (lhs r2), r <- rhs r1 ]

