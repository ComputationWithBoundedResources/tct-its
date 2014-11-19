{-# LANGUAGE ScopedTypeVariables #-}

-- local size bound
-- Sl(t,v')(m) >= sup { |v'(v)| exists l,v,l',v' . v <= m /\ (l,v) -> (l',v') for all |t,v'|
-- in other the lhs is a bound (as linear expression) on a rhs variable

-- should be computable as long we have linear bounds
-- has to be computed only once

module Tct.Its.Data.LocalSizebounds 
  (
  LocalSizebounds
  , compute
  , module Tct.Its.Data.Bounds 
  ) where

import Control.Monad (liftM, foldM)
import qualified Data.Map.Strict as M

import qualified SmtLib.Logic.Core                   as SMT
import qualified SmtLib.Logic.Int                    as SMT
import qualified SmtLib.SMT                          as SMT
import qualified SmtLib.Solver                       as SMT

import qualified Tct.Common.Polynomial               as P
import           Tct.Common.Ring
import qualified Tct.Common.SMT                      ()

import Tct.Its.Data.Cost
import Tct.Its.Data.Rule
import Tct.Its.Data.Bounds
import Tct.Its.Data.Types


type APoly = P.Polynomial SMT.Expr Var
type IPolyV = P.PolynomialView Int Var

compute :: Vars -> Rules -> IO LocalSizebounds
compute vs = foldM k empty
  where
    k sbs ir = union sbs `liftM` compute' vs ir lpoly
    lpoly    = P.linear (const (1 :: Int)) vs
    
compute' :: Vars -> (Int,Rule) -> IPolyV -> IO LocalSizebounds
compute' vs ir lpoly = M.fromList `liftM` mapM k (rvss vs ir)
  where k (rv,rpoly,cpolys) = entscheide lpoly rpoly cpolys >>= \c -> return (rv,c)

rvss :: Vars -> (Int, Rule) -> [(RV, IPoly, [APoly])]
rvss vs (ruleIdx, Rule _ rs cs) = 
  [ ((ruleIdx,rhsIdx,v),rpoly, cs')
    | (rhsIdx, r) <- zip [0..] rs, (v, rpoly) <- zip vs (args r) ]
  where cs' = [ P.mapCoefficients num' p | Gte p _ <- filterLinear (toGte cs) ]

num' :: Int -> SMT.Expr
num' i = if i < 0 then SMT.nNeg (SMT.num (-i)) else SMT.num i

instance (SMT.Decode m c a, Additive a, Eq a) 
  => SMT.Decode m (P.PolynomialView c Var) (P.Polynomial a Var) where
  decode = P.fromViewWithM SMT.decode

entscheide :: IPolyV -> IPoly -> [APoly] -> IO Cost
entscheide lview rpoly cpolys = do
  res :: SMT.Sat IPoly <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"

    apoly <- do
      let P.PolyV ts = lview
      P.PolyV `liftM` mapM (\(_,m) -> SMT.ivar >>= \c' -> return (c',m)) ts

    let
      interpretLhs = P.fromViewWith SMT.fm 
      interpretRhs = P.mapCoefficients num'
      absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]
    
    let
      bounded = (interpretLhs apoly `sub` interpretRhs rpoly) `eliminate` cpolys

      eliminate ply css = do
        let
          nvar' = SMT.fm `liftM` SMT.nvar
          k p = nvar' >>= \lambda -> return (lambda `P.scale` p)
        cs2 <- mapM k css
        let
          (p1,pc1) = P.splitConstantValue ply
          (p2,pc2) = P.splitConstantValue (bigAdd cs2)
        return $ absolute (p1 `sub` p2) SMT..&& (pc1 SMT..>= pc2)

    SMT.assert =<< bounded
    return $ SMT.decode apoly
  return $ mkCost res
  where
    mkCost res = case res of
      SMT.Sat p -> poly p
      _         -> omega
        
