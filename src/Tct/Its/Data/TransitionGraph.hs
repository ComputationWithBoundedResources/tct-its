module Tct.Its.Data.TransitionGraph 
  (
  TGraph
  , estimateGraph 
  , predecessors
  ) where


import qualified Data.Graph.Inductive as Gr

import Tct.Its.Data.Types

-- | Default estimation.
estimateGraph :: Rules -> TGraph
estimateGraph = estimateGraphWith functionSymbols

-- rule labels actually used?

estimateGraphWith :: (Rule -> Rule -> [Int])  -> Rules -> TGraph
estimateGraphWith f rs = Gr.mkGraph rs es
  where es  = [ (n1, n2, rhsIdx) | (n1,r1) <- rs, (n2,r2) <- rs, rhsIdx <- f r1 r2 ]

-- | only compares function symbols
functionSymbols :: Rule -> Rule -> [Int]
functionSymbols r1 r2 = [ rhsIdx | (r,rhsIdx) <- zip (rhs r1) [0..], fun r == fun (lhs r2) ]

predecessors :: TGraph -> RuleId -> [(RuleId, Int)]
predecessors = Gr.lpre

