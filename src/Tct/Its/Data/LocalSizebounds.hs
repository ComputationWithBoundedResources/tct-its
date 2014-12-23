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
  -- * Queries
  , lboundOf
  , lgrowthOf
  ) where


import           Control.Monad         (foldM, liftM)
import           Data.Maybe (fromMaybe)
import qualified Data.Map.Strict       as M

import qualified SLogic.Smt as SMT

import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Common.Polynomial as P
import           Tct.Common.Ring

import           Tct.Its.Data.Smt ()
import           Tct.Its.Data.Cost
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Types


{-instance PP.Pretty SMT.Expr where-}
  {-pretty = PP.text . SMT.prettyExpr-}



type LocalSizebounds = M.Map RV (Cost, Growth)

type APoly  = P.Polynomial SMT.IExpr Var
type IPolyV = P.PView Int Var


lboundOf :: LocalSizebounds -> RV -> Cost
lboundOf lbounds rv = fst (error err `fromMaybe` M.lookup rv lbounds)
  where err = "Tct.Its.Data.LocalSizebounds.lboundOf: key '" ++ show rv ++ "' not defined."

lgrowthOf :: LocalSizebounds -> RV -> Growth
lgrowthOf lbounds rv = snd (error err `fromMaybe` M.lookup rv lbounds)
  where err = "Tct.Its.Data.LocalSizebounds.lgrowthOf: key '" ++ show rv ++ "' not defined."


-- FIXME: require strongly linear interpretations as all other do not fit in current Growth classes
-- use linear programming for minimisation; check if localbound can be negative;
compute :: Vars -> Rules -> IO LocalSizebounds
compute vs = foldM k M.empty
  where
    k sbs ir = M.union sbs `liftM` compute' vs ir lpoly
    lpoly    = P.linear (const (1 :: Int)) vs

compute' :: Vars -> (Int,Rule) -> IPolyV -> IO LocalSizebounds
compute' vs ir lpoly = M.fromList `liftM` mapM k (rvss vs ir)
  where k (rv,rpoly,cpolys) = entscheide lpoly rpoly cpolys >>= \c -> return (rv,c)

rvss :: Vars -> (Int, Rule) -> [(RV, IPoly, [APoly])]
rvss vs (ruleIdx, Rule _ rs cs) =
  [ (RV ruleIdx rhsIdx v,rpoly, cs')
    | (rhsIdx, r) <- zip [0..] rs, (v, rpoly) <- zip vs (args r) ]
  where cs' = [ P.mapCoefficients SMT.num p | Gte p _ <- filterLinear (toGte cs) ]

instance (SMT.Decode m c a, Additive a, Eq a)
  => SMT.Decode m (P.PView c Var) (P.Polynomial a Var) where
  decode = P.fromViewWithM SMT.decode

entscheide :: IPolyV -> IPoly -> [APoly] -> IO (Cost, Growth)
entscheide lview rpoly cpolys = do
  res <- entscheide' lview rpoly cpolys False
  case res of
    SMT.Sat (lp,ap) -> return $ let r = poly lp `maximal` poly ap in (r,growth r)
    _         -> do 
      res' <- entscheide' lview rpoly cpolys False
      return $ case res' of 
        SMT.Sat (lp,ap) -> let r = poly lp `maximal` poly ap in (r,growth r)
        _         -> (Unknown,Unbounded)

  -- TODO: alternative instance for sat


entscheide' :: IPolyV -> IPoly -> [APoly] -> Bool -> IO (SMT.Result (IPoly,IPoly))
entscheide' lview rpoly cpolys withZeroConstant = do
  res :: SMT.Result (IPoly,IPoly) <- SMT.solveStM (SMT.minismt' ["-m", "-ib", "1"]) $ do
    SMT.setFormat "QF_LIA"

    let
      interpretLhs = P.fromViewWith id
      interpretRhs = P.mapCoefficients SMT.num
      absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]

    let
      rinst = interpretRhs rpoly
      eliminate ply css = do
        let
          k p = SMT.nvarM' >>= \lambda -> return (lambda `P.scale` p)
        cs2 <- mapM k css
        let
          (p1,pc1) = P.splitConstantValue ply
          (p2,pc2) = P.splitConstantValue (bigAdd cs2)
        return $ absolute (p1 `sub` p2) SMT..&& (pc1 SMT..>= pc2)

      restrictVar (_,m) 
        | null (P.mvariables m) = SMT.ivarM' >>= \c' -> return (c',m)
        | otherwise             = SMT.sivarM' >>= \c' -> return (c',m)


    -- upper bound 
    uapoly <- mapM restrictVar lview
    let ubounded = (interpretLhs uapoly `sub` rinst) `eliminate` cpolys
    
    -- lower bound
    lapoly <- mapM restrictVar lview
    let lbounded = (rinst `sub` interpretLhs lapoly) `eliminate` cpolys

    SMT.assert =<< ubounded
    SMT.assert =<< lbounded

    return $ SMT.decode (lapoly, uapoly)
  return res



ppLocalSizebounds :: Vars -> LocalSizebounds -> PP.Doc
ppLocalSizebounds vars lbounds = ppRVs vars (M.assocs lbounds) ppLbound
  where ppLbound (lbound, lgrowth)  = [PP.pretty lbound, PP.comma, PP.space, PP.pretty lgrowth]
  

instance PP.Pretty (Vars, LocalSizebounds) where
  pretty = uncurry ppLocalSizebounds

