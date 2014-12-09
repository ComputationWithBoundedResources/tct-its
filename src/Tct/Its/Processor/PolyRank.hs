{-# LANGUAGE ScopedTypeVariables #-}

{-

some explanation of the encoding does not hurt:

Linear ranking functions based on the farkas lemma [1,2]:

example:

forall X.
a1*x+b1*y+c1 >=0
a2*x+b2*y+c2 >=0
==> a'*x+b'y+c' >=0

exist la1, la2 >=0
a' = la1*a1+la2*a2 /\ b' = la1*b1+la2*b2 /\ c' >= la1*c1+la2+c2
Basically we just multiply each constraint with a fresh lambda symbol and sum them up.
Then we establish equality constraints between the coefficients of a variable and an inequality constraint for the constant part.
The farkas lemma states the equivalence of the forall an exist formula.


Polynomial ranking functions based on generalised farkas lemma [3]:
Sum_i p_i > 0 and Sum_j p_j >= 0 is unsat if there exists non-negative mu_0, mu_i, mu_j
where one of mu_0, mu_i is positive st
mu_0 + Sum_i mu_i*p_i + Sum_j mu_j*p_j = 0
decrease:
forall X . And p_i(X) >= 0 => l(X) - r(X) > 0
-> forall X . not (And p_i(X) >= 0) or l(X) - (r(x) + strict) >= 0
-> not(not (And p_i(X) >= 0) or l(X) - (r(x) + strict) >= 0) is unsat
-> (And p_i(X) >= 0) and not(l(X) - (r(x) + strict) >= 0)) is unsat
-> (And p_i(X) >= 0) and r(X) + strict - l(x) > 0) is unsat
-> mu_0 + mu_1*(r(X) - l(x)) + mu_j*p_i(X) = 0
bounded :
forall X . And p_i(X) >= 0 => l(X) > 0
-> forall X . And p_i(X) >= 0 => l(X) - 1 >= 0
-> (And p_i(X) and 1 - l(X) > 0) is unsat


[1] R. Bagnara, F. Mesnard. Eventual Linear Ranking Functions.
[2] A. Podelski and A.Rybalchenko. A Complete Method for the Synthesis of Linear Ranking Functions.
[3] Gulwani, A. Tiwari. Constrainted-based Approach for Analysis of Hybrid Systems.
-}

module Tct.Its.Processor.PolyRank 
  ( 
  polyRankProcessor
  
  , linear
  , mixed
  , polyDeclaration
  
  , farkas
  , farkasDeclaration

  , timebounds

  ) where

import           Control.Monad                       (liftM, when)
import           Control.Monad.Trans                 (liftIO)
import qualified Data.List                           as L (partition, intersect)
import           Data.Maybe                          (fromJust, fromMaybe, isJust)
import qualified Data.Map.Strict                     as M
import qualified Data.Set as S (empty)
import qualified Data.Traversable                    as T (mapM)

import qualified SmtLib.Logic.Core                   as SMT
import qualified SmtLib.Logic.Int                    as SMT
import qualified SmtLib.SMT                          as SMT
import qualified SmtLib.Solver                       as SMT

import qualified Tct.Core.Common.Pretty              as PP
import           Tct.Core.Data                       hiding (linear)

import           Tct.Common.ProofCombinators 
import qualified Tct.Common.Polynomial               as P
import qualified Tct.Common.PolynomialInterpretation as PI
import           Tct.Common.Ring
import qualified Tct.Common.SMT                      ()

import qualified Tct.Its.Data.Cost                   as C
import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Types
import qualified Tct.Its.Data.Timebounds             as TB
import qualified Tct.Its.Data.Sizebounds             as SB
import qualified Tct.Its.Data.TransitionGraph        as TG


--- Instances --------------------------------------------------------------------------------------------------------
poly :: PI.Shape -> Strategy Its
poly shp = Proc polyRankProcessor{ shape = shp}

farkas :: Strategy Its
farkas = Proc polyRankProcessor { useFarkas = True, shape = PI.Linear }

timebounds :: [RuleId] -> Strategy Its
timebounds rs = Proc polyRankProcessor { useFarkas = True, shape = PI.Linear, withSizebounds = rs }


polyDeclaration ::Declaration ('[ Argument 'Required PI.Shape ] :-> Strategy Its)
polyDeclaration = declare "poly" ["(non-liear) polynomial ranking function."] (OneTuple PI.shapeArg) poly

farkasDeclaration ::Declaration ('[] :-> Strategy Its)
farkasDeclaration = declare "farkas" ["linear polynomial ranking function."] () farkas

stronglyLinear, linear, quadratic :: Strategy Its
stronglyLinear = Proc polyRankProcessor{ shape = PI.StronglyLinear }
linear         = Proc polyRankProcessor{ shape = PI.Linear }
quadratic      = Proc polyRankProcessor{ shape = PI.Quadratic }

mixed :: Int -> Strategy Its
mixed i = Proc polyRankProcessor{ shape = PI.Mixed i }


data PolyRankProcessor = PolyRank
  { useFarkas      :: Bool -- implies linear shape
  , withSizebounds :: [RuleId]
  , shape          :: PI.Shape
  } deriving Show

polyRankProcessor :: PolyRankProcessor
polyRankProcessor = PolyRank
  { useFarkas      = False
  , withSizebounds = []
  , shape          = PI.Linear }

type PolyInter   = PI.PolyInter Fun Int
type IntPoly        = P.Polynomial Int Var
type Coefficient = PI.CoefficientVar Fun

data PolyOrder = PolyOrder
  { shape_   :: PI.Shape
  , pint_    :: PolyInter
  , strict_  :: [(Rule, IntPoly, IntPoly)]
  , weak_    :: [(Rule, IntPoly, IntPoly)]
  , times_   :: TB.Timebounds
  , sbounds_ :: Maybe (Vars, SB.Sizebounds)
  } deriving Show

data PolyRankProof = PolyRankProof (ApplicationProof (OrientationProof PolyOrder)) deriving Show

instance PP.Pretty PolyRankProcessor where pretty = PP.text . show
instance PP.Pretty PolyOrder where
  pretty order = PP.vcat $ 
    [ PP.text "We apply a polynomial interpretation of shape" PP.<+> PP.pretty (shape_ order) PP.<> PP.char ':'
    , PP.indent 2 (PP.pretty (pint_ order))
    , PP.text ""
    , PP.text "Following rules are strictly oriented:"
    , ppOrder (PP.text "   > ") (strict_ order)
    , PP.text ""
    , PP.text "Following rules are weakly oriented:"
    , ppOrder (PP.text "  >= ") (weak_ order) ]
    ++ maybe [PP.empty] (ppWithSizebounds) (sbounds_ order)
    where
      ppWithSizebounds vsbounds = 
        [ PP.text "We use the following global sizebounds:"
        , PP.pretty vsbounds]
      ppOrder ppOrd rs = PP.table [(PP.AlignRight, as), (PP.AlignLeft, bs), (PP.AlignLeft, cs)]
        where
          (as,bs,cs) = unzip3 $ concatMap ppRule rs
          ppRule (r, instlhs,instrhs) =
            [ (PP.pretty (con r)              , PP.text " ==> " , PP.empty)
            , (PP.indent 2(PP.pretty (lhs r)) , PP.text "   = " , PP.pretty instlhs)
            , (PP.empty                       , ppOrd           , PP.pretty instrhs)
            , (PP.empty                       , PP.text "   = " , PP.pretty (rhs r))
            , (PP.empty                       , PP.empty        , PP.empty) ]

instance PP.Pretty PolyRankProof where
  pretty (PolyRankProof o) = PP.pretty o

instance Processor PolyRankProcessor where
  type ProofObject PolyRankProcessor = PolyRankProof
  type Problem PolyRankProcessor     = Its
  solve p prob
    | closed prob = return $ resultToTree p prob $ Fail (PolyRankProof . Applicable $ Empty)
    | otherwise = do
        res  <- liftIO $ entscheide p prob
        return . resultToTree p prob $ case res of
          SMT.Sat order ->
            Success (Id $ updateTimebounds prob (times_ order)) (PolyRankProof $ Applicable $ Order order) (\(Id c) -> c)
          SMT.Error s -> Fail (PolyRankProof $ Inapplicable s)
          _ -> Fail (PolyRankProof . Applicable $ Incompatible)



newtype Strict = Strict { unStrict :: Int }
  deriving (Eq, Ord, Show)

num' :: Int -> SMT.Expr
num' i = if i < 0 then SMT.nNeg (SMT.num (-i)) else SMT.num i


find :: (Ord k, Show k) => M.Map k a -> k -> a
find m k = error err `fromMaybe` M.lookup k m
  where err = "Tct.Its.Processor.PolyRank: key " ++ show k ++ " not found."

entscheide :: PolyRankProcessor -> Its -> IO (SMT.Sat PolyOrder)
entscheide proc prob@(Its
  { _startterm       = startterm
  , _tgraph          = tgraph
  , _timebounds      = timebounds
  , _sizebounds      = sizebounds
  }) = do
  res :: SMT.Sat (M.Map Coefficient Int, M.Map Strict Int) <- SMT.solve SMT.minismt $ do
    SMT.setLogic "QF_NIA"
    -- TODO: memoisation is here not used
    (ebsi,coefficientEncoder) <- SMT.memo $ PI.PolyInter `liftM` T.mapM encode absi
    (_, strictVarEncoder) <- SMT.memo $ mapM  (SMT.snvarm . Strict) (indices somerules)

    let
      strict = SMT.fm . (strictVarEncoder `find`) . Strict
      interpretLhs    = interpret ebsi
      interpretRhs ts = interpret ebsi (head ts) -- TODO
      interpretCon cs = [ P.mapCoefficients num' c | Gte c _ <- toGte cs ]
      absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]


    let -- generalised farkas
      decrease (i,(Rule l rs cs)) = pl `eliminate` (interpretCon cs)
        where  pl = (interpretRhs rs `add` (P.constant $ strict i)) `sub` interpretLhs l
      bounded (Rule l _ cs) = eliminate pl (interpretCon cs)
        where pl = neg $ interpretLhs l `sub` P.constant one
      eliminate p ps = do
        let nvar' = SMT.fm `liftM` SMT.nvar
        mu0 <- nvar'
        mu1 <- nvar'
        SMT.assert $ mu0 SMT..> SMT.zero SMT..|| mu1 SMT..> SMT.zero
        mui <- mapM (\_ -> P.constant `liftM` nvar') [1..length ps]
        return $ absolute $ bigAdd $ P.constant mu0 : (P.constant mu1 `mul` p) : (zipWith mul mui ps)

    let -- farkas
      -- TODO: handle non-linear expressions on rhs
      decreaseFarkas (i,(Rule l rs cs)) = pl `eliminateFarkas`(interpretCon $ filterLinear cs)
        where pl = interpretLhs l `sub` (interpretRhs rs `add` P.constant (strict i))
      boundedFarkas (Rule l _ cs) = pl `eliminateFarkas`(interpretCon $ filterLinear cs)
        where pl = interpretLhs l `sub` P.constant one

      eliminateFarkas ply cs = do
        let
          nvar' = SMT.fm `liftM` SMT.nvar
          k p = nvar' >>= \lambda -> return (lambda `P.scale` p)
        cs2 <- mapM k cs
        let
          (p1,pc1) = P.splitConstantValue ply
          (p2,pc2) = P.splitConstantValue (bigAdd cs2)
        return $ absolute (p1 `sub` p2) SMT..&& (pc1 SMT..>= pc2)


    let
      order (i,r) = do
        fm1 <- if useFarkas proc then decreaseFarkas (i,r) else decrease (i,r)
        fm2 <- if useFarkas proc then boundedFarkas r else bounded r
        return (fm1 SMT..&& ((strict i SMT..> SMT.zero) SMT..==> fm2))

      orderConstraint = [ order r | r <- somerules ]
      rulesConstraint = [ strict i SMT..> SMT.zero | i <- strictrules ]

    let
      undefinedVars = computeUndefinedVars tgraph allrules somerules (fromJust sizebounds)
      undefinedCofs (Rule l _ _) = [ c | (c,ms) <- pl, (v,_) <- ms, isUndefined (fun l) v ]
        where
          pl = P.toView' (interpretLhs l)
          isUndefined f v = case M.lookup f undefinedVars of
            Nothing -> False
            Just vs -> v `elem` vs
      undefinedConstraint 
        | withSize  = SMT.bigAnd [ c SMT..== SMT.zero | (_,r) <- somerules, c <- undefinedCofs r ]
        | otherwise = SMT.top



    SMT.assert =<< bigAndM orderConstraint
    SMT.assert $ SMT.bigOr rulesConstraint
    SMT.assert $ undefinedConstraint



    return $ SMT.decode (coefficientEncoder, strictVarEncoder)

  return $ mkOrder `fmap` res
  where
    bigAndM = liftM SMT.bigAnd . sequence

    withSize = not $ null (withSizebounds proc)
    allrules = _irules prob
    somerules
      | withSize  = map (allrules !!) (withSizebounds proc)
      | otherwise = allrules
    strictrules = TB.nonDefined timebounds `L.intersect` fst (unzip somerules)
    encode = P.fromViewWithM (\c -> SMT.fm `liftM` SMT.ivarm c) -- FIXME: incorporate restrict var for strongly linear
        {-| PI.restrict c = SMT.fm `liftM` SMT.sivarm c-}
        {-| otherwise     = SMT.fm `liftM` SMT.nvarm c-}
    absi = M.mapWithKey (curry (PI.mkInterpretation kind)) sig
    kind = PI.ConstructorBased shp S.empty 
    sig = _signature prob
    shp = if useFarkas proc then PI.Linear else shape proc

    interpret ebsi = interpretTerm interpretFun interpretArg
      where
        interpretFun f = P.substituteVariables interp . M.fromList . zip [PI.SomeIndeterminate 0..]
          where interp = PI.interpretations ebsi `find` f
        interpretArg a = P.mapCoefficients num' a

    mkOrder (inter, stricts) = PolyOrder
      { shape_  = shp
      , pint_   = PI.PolyInter pint
      , strict_ = map (\(_,r) -> (r, inst (lhs r), bigAdd $ map inst (rhs r))) strictList
      , weak_   = map (\(_,r) -> (r, inst (lhs r), bigAdd $ map inst (rhs r))) weakList
      , times_  = times 
      , sbounds_ = if withSize then (\sb -> (domain prob, sb)) `fmap` sizebounds else Nothing}
      where
        strictMap = M.mapKeysMonotonic unStrict $ M.filter (>0) stricts
        (strictList, weakList) = L.partition (\(i,_) -> i `M.member` strictMap) somerules
        pint  = M.map (P.fromViewWith (inter `find`)) absi
        costs
          | withSize = computeBoundWithSize tgraph allrules somerules timebounds (fromJust $ sizebounds) costf 
          | otherwise = C.poly (inst $ startterm)
          where costf f = C.poly . inst $ Term f (args $ startterm)

        times = M.map (const costs) strictMap

        inst = interpretTerm interpretFun interpretArg
        interpretFun f = P.substituteVariables (pint `find` f) . M.fromList . zip [PI.SomeIndeterminate 0..]
        interpretArg a = a

computeUndefinedVars :: TG.TGraph -> Rules -> Rules -> SB.Sizebounds -> M.Map Fun [Var]
computeUndefinedVars tgraph allrules somerules sbounds = M.fromList
  [ (f,vs) | (t,i) <- ins, let f = funOf (t,i), let vs = M.keys $ M.filter (==C.Unknown) (SB.boundsOfVars sbounds (t,i))]
  where
    ins   = TG.incoming tgraph (fst $ unzip somerules) 
    funOf (t,i) = fun . (!! i) . rhs . snd $ allrules !! t

computeBoundWithSize :: TG.TGraph -> Rules -> Rules -> TB.Timebounds -> SB.Sizebounds -> (Fun -> C.Cost) -> C.Cost
computeBoundWithSize tgraph allrules somerules tbounds sbounds prf = bigAdd $ do
  (t,i) <- TG.incoming tgraph (fst $ unzip somerules)
  let
    innerTBound = prf (fun . (!! i) . rhs . snd $ allrules !! t)
    outerTBound = tbounds `TB.boundOf` t
    innerSBounds = SB.boundsOfVars sbounds (t,i)
  return $ outerTBound `mul` C.compose innerTBound innerSBounds


