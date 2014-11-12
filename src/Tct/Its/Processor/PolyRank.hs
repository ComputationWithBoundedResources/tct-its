{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Its.Processor.PolyRank where

import Control.Monad (liftM)
import Control.Monad.Trans (liftIO)
import qualified Data.Traversable as T (mapM)
import qualified Data.Map.Strict as M

import qualified SmtLib.Logic.Core                   as SMT
import qualified SmtLib.Logic.Int                    as SMT
import qualified SmtLib.SMT                          as SMT
import qualified SmtLib.Solver                       as SMT

import qualified Tct.Core.Common.Pretty as PP
import Tct.Core.Data

import qualified Tct.Common.SMT ()
import           Tct.Common.Ring
import           Tct.Common.Orientation
import qualified Tct.Common.Polynomial as P
import qualified Tct.Common.PolynomialInterpretation as PI

import Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds as TB
import qualified Tct.Its.Data.Cost as C
import Tct.Its.Data.Problem


--- Instances --------------------------------------------------------------------------------------------------------
poly :: PI.Shape -> Strategy Its
poly = Proc . PolyRank


polyDeclaration ::Declaration ('[ Argument 'Required PI.Shape ] :-> Strategy Its)
polyDeclaration = declare "poly" ["(non-liear) polynomial ranking function."] (OneTuple PI.shapeArg) poly

stronglyLinear, linear, quadratic :: Strategy Its
stronglyLinear = Proc (PolyRank PI.StronglyLinear)
linear         = Proc (PolyRank PI.Linear)
quadratic      = Proc (PolyRank PI.Quadratic)

mixed :: Int -> Strategy Its
mixed = Proc . PolyRank . PI.Mixed


data PolyRankProcessor = PolyRank 
  { shape :: PI.Shape
  } deriving Show

type PolyInter   = PI.PolyInter Fun Int
type Coefficient = PI.CoefficientVar Fun

data PolyOrder = PolyOrder
  { rules_ :: [Rule] 
  , inter_ :: PolyInter
  } deriving Show

data PolyRankProof = PolyRankProof (OrientationProof PolyOrder) deriving Show

instance PP.Pretty PolyRankProcessor where pretty = PP.text . show
instance PP.Pretty PolyOrder where 
  pretty (PolyOrder rs pint) = PP.vcat
    [ PP.text "PRF:"
    , PP.indent 2 (PP.pretty pint) 
    , PP.vcat [PP.pretty (interpret pint l) PP.<+> PP.text ">(=)" PP.<+> PP.pretty (interpret pint (head r)) | Rule l r _ <- rs ] ]
    where
      interpret pint t = C.poly $ interpretTerm interpretFun interpretArg t
        where
          interpretFun f = P.substituteVars (PI.interpretations pint M.! f) . M.fromList . zip [PI.SomeIndeterminate 0..]
          interpretArg a = a 

instance PP.Pretty PolyRankProof where
  pretty (PolyRankProof o) = PP.pretty o

instance Processor PolyRankProcessor where
  type ProofObject PolyRankProcessor = PolyRankProof
  type Problem PolyRankProcessor     = Its
  solve p prob 
    | closed prob = return $ resultToTree p prob $ Fail (PolyRankProof Empty)
    | otherwise = do
        res <- liftIO $ entscheide p prob
        return . resultToTree p prob $ case res of
          SMT.Sat (times, order) ->
            Success (Id $ updateTimebounds prob times) (PolyRankProof $ Order order) (\(Id c) -> c)
          SMT.Error s -> Fail (PolyRankProof $ Inapplicable s)
          _ -> Fail (PolyRankProof $ Incompatible)



newtype Strict = Strict { unStrict :: Rule }
  deriving (Eq, Ord, Show)

num' :: Int -> SMT.Expr
num' i = if i < 0 then SMT.nNeg (SMT.num (-i)) else SMT.num i

-- encoding: Constrainted-based Approach for Analysis of Hybrid Systems, Gulwani and Tiwari
-- Sum_i p_i > 0 and Sum_j p_j >= 0 is unsat if there exists non-negative mu_0, mu_i, mu_j
-- where one of mu_0, mu_i is positive st
-- mu_0 + Sum_i mu_i*p_i + Sum_j mu_j*p_j = 0
-- decrease: 
-- forall X . And p_i(X) >= 0 => l(X) - r(X) > 0
-- -> forall X . not (And p_i(X) >= 0) or l(X) - (r(x) + strict) >= 0
-- -> not(not (And p_i(X) >= 0) or l(X) - (r(x) + strict) >= 0) is unsat
-- -> (And p_i(X) >= 0) and not(l(X) - (r(x) + strict) >= 0)) is unsat
-- -> (And p_i(X) >= 0) and r(X) + strict - l(x) > 0) is unsat
-- -> mu_0 + mu_1*(r(X) - l(x)) + mu_j*p_i(X) = 0
-- bounded : 
-- forall X . And p_i(X) >= 0 => l(X) > 0
-- -> forall X . And p_i(X) >= 0 => l(X) - 1 >= 0
-- -> (And p_i(X) and 1 - l(X) > 0) is unsat
entscheide :: PolyRankProcessor -> Its -> IO (SMT.Sat (TB.Timebounds, PolyOrder))
entscheide proc prob = do
  res :: SMT.Sat (M.Map Coefficient Int, M.Map Strict Int) <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    (svars, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarm . Strict) allrules

    let
      strict = SMT.fm . (strictVarEncoder M.!) . Strict
      interpretLhs    = interpret ebsi
      interpretRhs ts = interpret ebsi (head ts)
      interpretCon cs = [ P.mapCoefficients num' c | Gte c _ <- normalise cs ]

    let
      absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]

      order r = do
        fm1 <- decrease r
        fm2 <- bounded r
        return (fm1 SMT..&& ((strict r SMT..> SMT.zero) SMT..==> fm2))

      decrease r@(Rule l rs cs) = absolute `liftM` eliminate pl (interpretCon cs)
        where  pl = (interpretRhs rs `add` (P.constant $ strict r)) `sub` interpretLhs l
      bounded (Rule l _ cs) = absolute `liftM` eliminate pl (interpretCon cs)
        where pl = neg $ interpretLhs l `sub` P.constant one


      orderConstraint = [ order r | r <- allrules ]
      rulesConstraint = [ strict r SMT..> SMT.zero | r <- strictrules ]

    SMT.assert =<< bigAndM orderConstraint
    SMT.assert $ SMT.bigOr rulesConstraint

    return $ SMT.decode (coefficientEncoder, strictVarEncoder)
  return $ mkOrder `fmap` res
  where
    bigAndM = liftM SMT.bigAnd . sequence
    allrules = rules prob
    strictrules = TB.strict (timebounds prob)
    encode = P.pfromViewWithM (\c -> SMT.fm `liftM` SMT.ivarm c)
    absi = M.mapWithKey (curry (PI.mkInterpretation kind)) sig
    kind = PI.ConstructorBased shp []
    sig = signature prob
    shp = shape proc 

    interpret ebsi = interpretTerm interpretFun interpretArg
      where
        interpretFun f = P.substituteVars interp . M.fromList . zip [PI.SomeIndeterminate 0..]
          where interp = PI.interpretations ebsi M.! f
        interpretArg a = P.mapCoefficients num' a

    mkOrder (inter, stricts) = (times, PolyOrder allrules (PI.PolyInter pint))
      where
        stricts' = M.mapKeysMonotonic unStrict $ M.filter (>0) stricts
        pint  = M.map (P.pfromViewWith (inter M.!)) absi
        costs = C.poly $ interpretTerm interpretFun interpretArg (startterm prob)
        times = M.map (const costs) stricts'
        interpretFun f = P.substituteVars (pint M.! f) . M.fromList . zip [PI.SomeIndeterminate 0..]
        interpretArg a = a 

-- expects: (E A)(F X) /\ p_i >= 0 
eliminate :: Monad m => P.Polynomial SMT.Expr Var -> [P.Polynomial SMT.Expr Var] -> SMT.SMT m (P.Polynomial SMT.Expr Var)
eliminate p ps  = do
  let nvar' = SMT.fm `liftM` SMT.nvar
  mu0 <- nvar'
  mu1 <- nvar'
  SMT.assert $ mu0 SMT..> SMT.zero SMT..|| mu1 SMT..> SMT.zero
  mui <- mapM (\_ -> P.constant `liftM` nvar') [1..length ps]
  return $ bigAdd $ P.constant mu0 : (P.constant mu1 `mul` p) : (zipWith mul mui ps)

