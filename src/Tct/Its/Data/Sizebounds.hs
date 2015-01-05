module Tct.Its.Data.Sizebounds
  (
  Sizebounds
  , initialise
  , boundsOfVars

  , updateSizebounds
  , sizebound
  , sizebounds
  , module Tct.Its.Data.Bounds
  ) where

import qualified Data.Map.Strict as M
import qualified Data.List as L (intersect, nub, (\\))


import qualified Tct.Core.Common.Pretty as PP

import           Tct.Common.Ring
import qualified Tct.Common.Polynomial as P

import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import qualified Tct.Its.Data.ResultVariableGraph as RVG
import           Tct.Its.Data.TransitionGraph (TGraph)
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Complexity
import           Tct.Its.Data.Bounds
import           Tct.Its.Data.Timebounds (Timebounds)
import qualified Tct.Its.Data.Timebounds as TB
import           Tct.Its.Data.LocalSizebounds (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds as LB
import           Tct.Its.Data.Types

--import Debug.Trace

type Sizebounds = Bounds RV

initialise :: LocalSizebounds -> Sizebounds
initialise lbounds = foldl (\acc k -> M.insert k Unknown acc) M.empty (M.keys lbounds)

updateSizebounds :: TGraph -> RVGraph -> Timebounds -> Sizebounds -> LocalSizebounds -> Sizebounds
updateSizebounds tgraph rvgraph tbounds sbounds lbounds = foldl k sbounds (RVG.sccs rvgraph)
  where
    k nsbounds scc = case scc of
      RVG.Trivial rv    -> sizebound tgraph lbounds rv nsbounds
      RVG.NonTrivial rvs -> sizebounds tbounds nsbounds lbounds rvgraph rvs



boundsOfVars :: Sizebounds -> (Int,Int) -> M.Map Var Complexity
boundsOfVars sbounds (t1,i1) = M.fromList [ (v,c) | (RV  t i v ,c) <- M.assocs sbounds , t == t1, i == i1 ]

-- sizebound for trivial SCCs
sizebound :: TGraph -> LocalSizebounds -> RV -> Sizebounds -> Sizebounds
sizebound tgraph lbounds rv sbounds = update rv sbound sbounds
  where
    lbound = lbounds `LB.lboundOf` rv
    sbound
      | null preds = lbound
      | otherwise  = foldl1 maximal [ compose lbound (varmap t' i)| (t',i) <- preds ]

    varmap t' i = M.fromList [ (v1,c1) | (RV t1 i1 v1, c1) <- M.assocs sbounds , t1 == t', i1 == i ]
    preds       = TG.predecessors tgraph (rvRule rv) 

cyclicDependencies :: RVGraph -> [RV] -> RV -> [Var]
cyclicDependencies rvgraph scc rv = L.nub [ rvVar rv' | rv' <- RVG.predecessors rvgraph rv `L.intersect` scc ]

dependencyConstraint :: RVGraph -> [RV] -> RV -> Bool
dependencyConstraint rvgraph rvs rv = length (cyclicDependencies rvgraph rvs rv) <= 1

sizebounds :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> Sizebounds
sizebounds tbounds sbounds lbounds rvgraph scc 
  | not (null unbounds)                                         = sbounds
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
      


sizeboundOf :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> [(RV,Int)] -> [(RV,Int)] -> [(RV,Int)] -> Complexity
sizeboundOf tbounds sbounds lbounds rvgraph scc ms mps sps=
  sizeboundMax sbounds rvgraph scc ms
  `add` sizeboundMaxPlus tbounds mps
  `add` sizeboundSumPlus tbounds sbounds lbounds rvgraph scc sps

sizeboundsIncoming :: Sizebounds -> RVGraph -> [RV] -> [Complexity]
sizeboundsIncoming sbounds rvgraph = map (sbounds `boundOf`) . RVG.incoming rvgraph

sizeboundMax :: Sizebounds -> RVGraph -> [RV] -> [(RV,Int)] -> Complexity
sizeboundMax sbounds rvgraph scc ms = foldl1 maximal (constBound: incomBounds)
  where 
    constBound = poly . P.constant . maximum . (0:) . snd $ unzip ms
    incomBounds = sizeboundsIncoming sbounds rvgraph scc

-- | 
sizeboundMaxPlus :: Timebounds -> [(RV, Int)] -> Complexity
sizeboundMaxPlus tbounds mps = bigAdd $ map k mps
  where k (rv,i) = (tbounds `TB.tboundOf` rvRule rv) `mul` poly (P.constant i)


sizeboundSumPlus :: Timebounds -> Sizebounds -> LocalSizebounds -> RVGraph -> [RV] -> [(RV, Int)] -> Complexity
sizeboundSumPlus tbounds sbounds lbounds rvgraph scc sps = bigAdd $ map k sps
  where 
    k (rv,i) = (tbounds `TB.tboundOf` rvRule rv) `mul` ( poly (P.constant i) `add` bigAdd (map (f rv) (vars rv)))
    vars rv = activeVariables (lbounds `LB.lboundOf` rv) L.\\ cyclicDependencies rvgraph scc rv
    f rv v = foldl maximal zero [ sbounds `boundOf` rv' | rv' <- RVG.predecessors rvgraph rv, v == rvVar rv' ]

ppSizebounds :: Vars -> Sizebounds -> PP.Doc
ppSizebounds vars sbounds = ppRVs vars (M.assocs sbounds) (\sbound -> [PP.pretty sbound])

instance PP.Pretty (Vars,Sizebounds) where
  pretty = uncurry ppSizebounds

