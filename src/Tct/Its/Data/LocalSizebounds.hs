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
import qualified Data.Map.Strict       as M
import qualified Data.List       as L

import qualified SmtLib.Logic.Core     as SMT
import qualified SmtLib.Logic.Int      as SMT
import qualified SmtLib.SMT            as SMT
import qualified SmtLib.Solver         as SMT

import qualified Tct.Core.Common.Pretty     as PP
import qualified Tct.Common.Polynomial as P
import           Tct.Common.Ring
import qualified Tct.Common.SMT        ()

import           Tct.Its.Data.Cost
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Types


type LocalSizebounds = M.Map RV (Cost, Growth)

type APoly  = P.Polynomial SMT.Expr Var
type IPolyV = P.PView Int Var


lboundOf :: LocalSizebounds -> RV -> Cost
lboundOf lbounds rv = fst (lbounds M.! rv)

lgrowthOf :: LocalSizebounds -> RV -> Growth
lgrowthOf lbounds rv = snd (lbounds M.! rv)


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
  [ ((ruleIdx,rhsIdx,v),rpoly, cs')
    | (rhsIdx, r) <- zip [0..] rs, (v, rpoly) <- zip vs (args r) ]
  where cs' = [ P.mapCoefficients num' p | Gte p _ <- filterLinear (toGte cs) ]

num' :: Int -> SMT.Expr
num' i = if i < 0 then SMT.nNeg (SMT.num (-i)) else SMT.num i

instance (SMT.Decode m c a, Additive a, Eq a)
  => SMT.Decode m (P.PView c Var) (P.Polynomial a Var) where
  decode = P.fromViewWithM SMT.decode

entscheide :: IPolyV -> IPoly -> [APoly] -> IO (Cost, Growth)
entscheide lview rpoly cpolys = do
  res <- entscheide' lview rpoly cpolys True
  case res of
    SMT.Sat p -> return $ let r = poly p in (r,growth r)
    _         -> do 
      res' <- entscheide' lview rpoly cpolys True
      return $ case res' of 
        SMT.Sat p -> let r = poly p in (r,growth r)
        _         -> (Unknown,Unbounded)

  -- TODO: alternative instance for sat


entscheide' :: IPolyV -> IPoly -> [APoly] -> Bool -> IO (SMT.Sat IPoly)
entscheide' lview rpoly cpolys withZeroConstant = do
  res :: SMT.Sat IPoly <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"

    apoly <- mapM (\(_,m) -> SMT.ivar >>= \c' -> return (c',m)) lview

    let
      interpretLhs = P.fromViewWith SMT.fm
      interpretRhs = P.mapCoefficients num'
      absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]

    let
      linst
        | withZeroConstant = fst (P.splitConstantValue pl)
        | otherwise        = pl
        where pl = interpretLhs apoly
      bounded = (linst `sub` interpretRhs rpoly) `eliminate` cpolys


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
  return res


-- pretty printing

ppLocalSizebounds :: Vars -> LocalSizebounds -> PP.Doc
ppLocalSizebounds vars lbounds = PP.table [(PP.AlignLeft, ppc) | c <- cols, let ppc = map ppEntry c ] 
  where
    ppEntry (rv,(lbound,lgrowth)) = PP.tupled [PP.pretty rv, PP.pretty lbound, PP.pretty lgrowth]
    cols = mkPartition [] vars (M.assocs lbounds)
    mkPartition acc [] _       = reverse acc
    mkPartition acc (v:vs) es  = mkPartition (a:acc) vs es'
      where (a,es') = L.partition (\((_,_,v'),_) -> v == v') es

instance PP.Pretty (Vars, LocalSizebounds) where
  pretty = uncurry ppLocalSizebounds

