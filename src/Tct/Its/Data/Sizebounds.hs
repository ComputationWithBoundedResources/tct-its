module Tct.Its.Data.Sizebounds
  (
  Sizebounds
  , initialise
  , boundsOfVars

  , sizebound
  , sizebounds
  , module Tct.Its.Data.Bounds
  ) where

import qualified Data.Map.Strict as M
import qualified Data.List as L (intersect, nub, (\\))


import           Tct.Common.Ring
import qualified Tct.Common.Polynomial as P

import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import qualified Tct.Its.Data.ResultVariableGraph as RV
import           Tct.Its.Data.TransitionGraph (TGraph)
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Cost
import           Tct.Its.Data.Bounds
import           Tct.Its.Data.Timebounds (Timebounds)
import           Tct.Its.Data.LocalSizebounds (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds as LB
import           Tct.Its.Data.Types

type Sizebounds = Bounds RV

initialise :: Rules -> Sizebounds
initialise = error "Sizebounds.initialise: yet not implemented"


boundsOfVars :: Sizebounds -> (Int,Int) -> M.Map Var Cost
boundsOfVars sbounds (t1,i1) = M.fromList [ (v,c) | ((t,i,v),c) <- M.assocs sbounds , t == t1, i == i1 ]


-- sizebound for trivial SCCs
sizebound :: TGraph -> LocalSizebounds -> RV -> Sizebounds -> Sizebounds
sizebound tgraph lbounds rv@(t,_,_) sbounds = update rv sbound sbounds
  where
    lbound = lbounds `LB.lboundOf` rv
    sbound
      | null preds = lbound
      | otherwise  = foldl1 maximal [ compose lbound (varmap t' i)| (t',i) <- preds ]

    varmap t' i = M.fromList [ (v1,c1) | ((t1,i1,v1),c1) <- M.assocs sbounds , t1 == t', i1 == i ]
    preds       = TG.predecessors tgraph t

cyclicDependencies :: RVGraph -> [RV] -> RV -> [Var]
cyclicDependencies rvgraph scc rv = L.nub [ v | (_,_,v) <- RV.predecessors rvgraph rv `L.intersect` scc ]

dependencyConstraint :: RVGraph -> [RV] -> RV -> Bool
dependencyConstraint rvgraph rvs rv = length (cyclicDependencies rvgraph rvs rv) <= 1

sizebounds :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> Sizebounds
sizebounds tbounds sbounds lbounds rvgraph scc 
  | not (null unbounds)                                   = sbounds
  | not (all (dependencyConstraint rvgraph scc . fst) sumpluss) = sbounds
  | otherwise = foldl (\sbounds' rv -> update rv cost sbounds') sbounds scc
  where 
    (maxs,maxpluss,sumpluss,unbounds) = classify lbounds scc
    cost = sizeboundOf tbounds sbounds lbounds rvgraph scc maxs maxpluss sumpluss


-- sepereate in classes
classify :: LocalSizebounds -> [RV] -> ([(RV, Int)],[(RV, Int)],[(RV, Int)],[RV])
classify lbounds = foldl k ([],[],[],[])
  where
    k (ms, mps, sps, us) rv = case lbounds `LB.lgrowthOf` rv of
      Max i     -> ((rv,i):ms , mps        , sps        , us)
      MaxPlus i -> (ms        , (rv,i):mps , sps        , us)
      SumPlus i -> (ms        , mps        , (rv,i):sps , us)
      Unbounded -> (ms        , mps        , sps        , rv:us)
      


sizeboundOf :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> [(RV,Int)] -> [(RV,Int)] -> [(RV,Int)] -> Cost
sizeboundOf tbounds sbounds lbounds rvgraph scc ms mps sps=
  sizeboundMax sbounds rvgraph scc ms
  `add` sizeboundMaxPlus tbounds mps
  `add` sizeboundSumPlus tbounds sbounds lbounds rvgraph scc sps

sizeboundsIncoming :: Sizebounds -> RVGraph -> [RV] -> [Cost]
sizeboundsIncoming sbounds rvgraph = map (sbounds `boundOf`) . RV.incoming rvgraph

sizeboundMax :: Sizebounds -> RVGraph -> [RV] -> [(RV,Int)] -> Cost
sizeboundMax sbounds rvgraph scc ms = foldl1 maximal (constBound: incomBounds)
  where 
    constBound = poly . P.constant . maximum . snd $ unzip ms
    incomBounds = sizeboundsIncoming sbounds rvgraph scc

-- | 
sizeboundMaxPlus :: Timebounds -> [(RV,Int)] -> Cost
sizeboundMaxPlus tbounds mps = bigAdd $ map k mps
  where k ((t,_,_),i) = (tbounds `boundOf` t) `mul` poly (P.constant i)


sizeboundSumPlus :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> [(RV,Int)] -> Cost
sizeboundSumPlus tbounds sbounds lbounds rvgraph scc sps = bigAdd $ map k sps
  where 
    k (rv@(t,_,_),i) = (tbounds `boundOf` t) `mul` ( poly (P.constant i) `add` bigAdd (map (f rv) (vars rv)))
    vars rv = activeVariables (lbounds `LB.lboundOf` rv) L.\\ cyclicDependencies rvgraph scc rv
    f rv v = foldl maximal zero [ sbounds `boundOf` rv' | rv'@(_,_,v') <- RV.predecessors rvgraph rv, v == v' ]

