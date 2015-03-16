{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Its.Processor.TransitionPredicateAbstraction 
  ( transitionAbstraction
  , sizeChangePredicates
  , monotonicityPredicates
  ) where


import           Control.Applicative
import           Control.Monad.Trans                (liftIO)
import qualified Data.IntMap                        as IM
import qualified Data.Set                           as S

import qualified Tct.Core.Common.Pretty             as PP
import qualified Tct.Core.Common.Xml                as Xml
import qualified Tct.Core.Data                      as T

import qualified Tct.Common.Polynomial              as P
import           Tct.Common.ProofCombinators
import           Tct.Common.Ring
import qualified Tct.Common.SMT                     as SMT

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds            as TB
import qualified Tct.Its.Data.TransitionGraph            as TG
import           Tct.Its.Data.TransitionAbstraction
import           Tct.Its.Data.Types
import           Tct.Its.Processor.Simplification   (testUnsatRule)


type PVar = Either Var Var

toVar :: PVar -> Var
toVar (Left v)  = v
toVar (Right v) = v ++ "'"


data Predicates
  = Alt [Predicates] -- left biased alternative
  | Seq [Predicates] -- test all
  | Prd (AAtom PVar)
  deriving Show

postify :: ARule f Var -> ARule f PVar
postify r1@(Rule l [r] _) = Rule (lhs r2) [r'] cs
  where
    r2 = renameWith Left r1
    r' = r{args = map (P.rename Right) (args l)}
    cs = con r2 ++ zipWith Eq (args r') (args . head $ rhs r2)
postify _ = error "contains nested recursion"

abstractWith :: Predicates -> Abstraction IO Rule Rule
abstractWith ps r1@(Rule _ [_] _) =
  renameWith toVar . Rule (lhs r2) (rhs r2) <$> valids ps
  where
    r2 = postify r1

    valids (Alt []) = return []
    valids (Alt (p:px)) = valids p >>= \vs -> if null vs then valids (Alt px) else return vs
    valids (Seq px) = concat `fmap` mapM valids px
    valids (Prd p)  = isValid p >>= \b -> return [p | b]

    isValid (Gte p1 p2) = entscheide cpolys (P.mapCoefficients SMT.num $ p1 `sub` p2)
      where cpolys = [ P.mapCoefficients SMT.num c | Gte c _ <- toGte (con r2) ]
    isValid _           = return False

    entscheide cpolys poly  = do
      res :: SMT.Result () <- SMT.solveStM SMT.yices $ do
        SMT.setFormat "QF_LIA"

        let
          absolute p = SMT.bigAnd [ c SMT..== SMT.zero | c <- P.coefficients p ]
          eliminate ply css = do
            let
              k p = SMT.nvarM' >>= \lambda -> return (lambda `P.scale` p)
            css2 <- mapM k css
            let
              (p1,pc1) = P.splitConstantValue ply
              (p2,pc2) = P.splitConstantValue (bigAdd css2)
            return $ absolute (p1 `sub` p2) SMT..&& (pc1 SMT..>= pc2)

        SMT.assert =<< poly `eliminate` cpolys

        return $ SMT.decode ()
      return $ SMT.isSat res
abstractWith _ _ = error "constains nested recursion"

transformWith :: Predicates -> Transformer IO Rule Rule
transformWith ps r1 r = do
  rM <- testUnsatRuleM (chain r1 r)
  case rM of
    Nothing -> return Nothing
    Just r2 -> Just `fmap` abstractWith ps r2
  where testUnsatRuleM = maybe (return Nothing) (\ru -> (testUnsatRule ru >>= \b -> return (if b then Nothing else Just ru)))

data TransitionAbstraction
  = Replacement { predicates :: Predicates, partial :: Maybe [RuleId]}
  deriving Show

data TransitionAbstractionProof
  = ReplacementProof
  | TransitionAbstractionFail
  deriving Show

instance T.Processor TransitionAbstraction where
  type ProofObject TransitionAbstraction = ApplicationProof TransitionAbstractionProof
  type Problem TransitionAbstraction = Its
  type Forking TransitionAbstraction = T.Optional T.Id

  solve p prob = do
    edges <- liftIO $ lfp abstract transform initials transitions
    let
      fresh = let m = maximum (IM.keys $ _irules prob) in [m..]
      lns   = (\(_,_,z) -> z) (unzip3 edges)

      irules = IM.fromList $ zip fresh (S.toList $ S.fromList lns)

      -- TODO: generalise probleminitialisation
      nprob = case partial p of
        Nothing -> prob
          { _irules          = irules
          , _tgraph          = TG.estimateGraph irules
          , _rvgraph         = Nothing
          , _timebounds      =
              TB.initialise (IM.keys irules) (IM.keys $ IM.filter (\r -> fun (lhs r) == sfun ) irules)
          , _sizebounds      = Nothing
          , _localSizebounds = Nothing }
          where sfun = fun (_startterm prob)
        Just _ -> undefined
      proof = ReplacementProof

    return $ progress p prob (Progress nprob) (Applicable proof)
      where
        abstract  = abstractWith (predicates p)
        transform = transformWith (predicates p)
        initials  = case partial p of
          Nothing -> rules (_irules prob)
          Just _ -> undefined
        transitions = case partial p of
          Nothing -> rules (_irules prob)
          Just _ -> undefined


--- * instances ------------------------------------------------------------------------------------------------------

transitionAbstraction :: Predicates -> T.Strategy Its
transitionAbstraction ps = T.Proc Replacement{ predicates=ps, partial=Nothing }

vsL, vsR :: Its -> [P.Polynomial Int (Either Var Var)]
vsL = map (P.rename Left . P.variable) . domain
vsR = map (P.rename Right . P.variable) . domain

gte, gt :: Ord v => AIPoly v -> AIPoly v -> AAtom v
gte   = Gte
gt p1 = Gte (p1 `sub` one)

sizeChangePredicates :: Its -> Predicates
sizeChangePredicates prob = Seq
  [ Seq [ Alt [ Prd (p1 `gt` p2), Prd(p1 `gte` p2) ] | p1 <- vs1, p2 <- vs2 ]
  , Seq [ Alt [ Prd (p1 `gt` zero), Prd (p1 `gte` zero)] | p1 <- vs1 ]
  , Seq [ Alt [ Prd (p2 `gt` zero), Prd (p2 `gte` zero)] | p2 <- vs2 ] ]
  where (vs1, vs2) = (vsL prob, vsR prob)

monotonicityPredicates :: Its -> Predicates
monotonicityPredicates prob = Seq
  [ Seq [ Alt [ Prd (p1 `gt` p2), Prd (p2 `gt` p1), Seq [ Prd (p1 `gte` p2), Prd (p2 `gte` p1) ] ] | p1 <- vs1, p2 <- vs2 ]
  , Seq [ Seq [ Prd (p1 `gte` zero), Prd (zero `gte` p1) ] | p1 <- vs1 ]
  , Seq [ Seq [ Prd (p2 `gte` zero), Prd (zero `gte` p2) ] | p2 <- vs2 ] ]
  where (vs1, vs2) = (vsL prob, vsR prob)


--- * proofdata ------------------------------------------------------------------------------------------------------

instance PP.Pretty TransitionAbstractionProof where
  pretty = const PP.empty

instance Xml.Xml TransitionAbstractionProof where
  toXml = const $ Xml.elt "" []

