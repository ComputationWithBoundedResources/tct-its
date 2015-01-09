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


import           Control.Monad         (liftM)
import           Data.Maybe (fromMaybe)
import qualified Data.IntMap.Strict       as IM
import qualified Data.Map.Strict       as M
import Data.List (intersect)

import qualified SLogic.Smt as SMT

import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Common.Polynomial as P
import           Tct.Common.Ring

import           Tct.Its.Data.Smt ()
import           Tct.Its.Data.Complexity
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Types


{-instance PP.Pretty SMT.Expr where-}
  {-pretty = PP.text . SMT.prettyExpr-}



type LocalSizebounds = M.Map RV (Complexity, Growth)

type APoly  = P.Polynomial SMT.IExpr Var
type IPolyV = P.PView Coefficient Var

data Coefficient
  = SomeCoefficient 
  | RestrictCoefficient 
  | IntCoefficient Int
  deriving (Eq,Ord,Show)


lboundOf :: LocalSizebounds -> RV -> Complexity
lboundOf lbounds rv = fst (error err `fromMaybe` M.lookup rv lbounds)
  where err = "Tct.Its.Data.LocalSizebounds.lboundOf: key '" ++ show rv ++ "' not defined."

lgrowthOf :: LocalSizebounds -> RV -> Growth
lgrowthOf lbounds rv = snd (error err `fromMaybe` M.lookup rv lbounds)
  where err = "Tct.Its.Data.LocalSizebounds.lgrowthOf: key '" ++ show rv ++ "' not defined."


compute :: Vars -> Rules -> IO LocalSizebounds
compute vs rs = M.unions `liftM` sequence (IM.foldrWithKey k [] rs)
  where k i r acc = computeRule vs (i,r) : acc

computeRule :: Vars -> (RuleId, Rule) -> IO LocalSizebounds
computeRule vs ir = M.fromList `liftM` mapM k (rvss vs ir)
  where k (rv,rpoly,cpolys) = computeVar vs rpoly cpolys >>= \c -> return (rv,c)

rvss :: Vars -> (RuleId, Rule) -> [(RV, IPoly, [APoly])]
rvss vs (ruleIdx, Rule _ rs cs) =
  [ (RV ruleIdx rhsIdx v,rpoly, cs')
    | (rhsIdx, r) <- zip [0..] rs, (v, rpoly) <- zip vs (args r) ]
  where cs' = [ P.mapCoefficients SMT.num p | Gte p _ <- filterLinear (toGte cs) ]

computeVar :: Vars -> IPoly -> [APoly] -> IO (Complexity, Growth)
computeVar vs rpoly cpolys = fromMaybe (error "computeVar") `liftM` foldl1 liftMPlus
  [ 
  -- direct
  return $ if null cs then Just (poly rpoly, Max (abs c)) else Nothing
  , return $ if rpoly' `elem` pvars then Just (poly rpoly, Max 0) else Nothing
  -- indirect simple
  , solveWith []
  , solveWith' commonvs
  , solveWith commonvs
  -- indirect
  , solveWith vs
  -- last resort
  , return  unbounded ]
  where 
    (cs,c)    = P.coefficients' rpoly
    pvars     = map P.variable vs
    rpoly'    = P.mapCoefficients abs rpoly
    unbounded = Just (Unknown, Unbounded)
    commonvs  = vs `intersect` P.variables rpoly

    solveWith ls = entscheide (P.linear k ls) rpoly cpolys
      where k m = if m == one then SomeCoefficient else RestrictCoefficient
    solveWith' [] = return Nothing
    solveWith' ls = entscheide (P.linear k ls) rpoly cpolys
      where k m = if m == one then IntCoefficient 0 else RestrictCoefficient
    liftMPlus m1 m2 = m1 >>= \m1' -> maybe m2 (return . Just) m1'


instance (SMT.Decode m c a, Additive a, Eq a)
  => SMT.Decode m (P.PView c Var) (P.Polynomial a Var) where
  decode = P.fromViewWithM SMT.decode

entscheide :: IPolyV -> IPoly -> [APoly] -> IO (Maybe (Complexity, Growth))
entscheide lview rpoly cpolys = do
  res <- entscheide' lview rpoly cpolys
  return $ case res of
    SMT.Sat (lp,ap) -> let r = poly lp `maximal` poly ap in Just (r,growth r)
    _               -> Nothing

entscheide' :: IPolyV -> IPoly -> [APoly] -> IO (SMT.Result (IPoly,IPoly))
entscheide' lview rpoly cpolys = do
  res :: SMT.Result (IPoly,IPoly) <- SMT.solveStM SMT.yices $ do
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

      restrictVar (SomeCoefficient,m)     = SMT.ivarM' >>= \c' -> return (c',m)
      restrictVar (RestrictCoefficient,m) = SMT.sivarM' >>= \c' -> return (c',m)
      restrictVar (IntCoefficient i,m)    = return (SMT.num i, m)


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

