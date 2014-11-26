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
import qualified Data.List as L (intersect, nub)


import           Tct.Common.Ring
import qualified Tct.Common.Polynomial as P

import qualified Tct.Its.Data.ResultVariableGraph as RV
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Cost
import           Tct.Its.Data.Bounds
import qualified Tct.Its.Data.LocalSizebounds as LB
import           Tct.Its.Data.Types


initialise :: Rules -> Sizebounds
initialise = error "Sizebounds.initialise: yet not implemented"


boundsOfVars :: Sizebounds -> (Int,Int) -> (M.Map Var Cost)
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

dependencyConstraint :: RVGraph -> [RV] -> RV -> Bool
dependencyConstraint rvgraph rvs rv = length dependencies <= 1
  where dependencies = L.nub $ [ v | (_,_,v) <- RV.predecessors rvgraph rv `L.intersect` rvs ]

sizebounds :: TGraph -> RVGraph -> LocalSizebounds -> [RV] -> Sizebounds -> Sizebounds
sizebounds tgraph rvgraph lbounds rvs sbounds
  | not (null unbounds)                                   = sbounds
  | not (all (dependencyConstraint rvgraph rvs . fst) sumpluss) = sbounds
  | otherwise = foldl (\sbounds' rv -> update rv (undefined) sbounds') sbounds rvs
  where 
    (maxs,maxpluss,sumpluss,unbounds) = classify lbounds rvs


-- sepereate in classes
classify :: LocalSizebounds -> [RV] -> ([(RV, Int)],[(RV, Int)],[(RV, Int)],[RV])
classify lbounds = foldl k ([],[],[],[])
  where
    k (ms, mps, sps, us) rv = case lbounds `LB.lgrowthOf` rv of
      Max i     -> ((rv,i):ms , mps        , sps        , us)
      MaxPlus i -> (ms        , (rv,i):mps , sps        , us)
      SumPlus i -> (ms        , mps        , (rv,i):sps , us)
      Unbounded -> (ms        , mps        , sps        , rv:us)
      


sizeboundOf :: RV -> Cost
sizeboundOf = undefined

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


sizeboundSumPlus :: LocalSizebounds -> RVGraph -> Timebounds -> [(RV,Int)] -> Cost
sizeboundSumPlus lbounds rvgraph tbounds = undefined







