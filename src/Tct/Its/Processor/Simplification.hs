module Tct.Its.Processor.Simplification
  (
  -- * Trivial SCCs
  boundTrivialSCCs
  , boundTrivialSCCsDeclaration

  -- * Knowledge Propagation
  , knowledgePropagation
  , knowledgePropagationDeclaration
  ) where


import qualified Data.Graph.Inductive         as Gr
import qualified Data.Map.Strict              as M

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Data                as T

import           Tct.Its.Data.Cost
import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds      as TB
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types


data PropagationProcessor
  = TrivialSCCs -- ^ Trivial SCCs in the transition graph are trivially bounded.
  | KnowledgePropagation
  deriving Show

data PropagationProof
  = PropagationProof
    { _proc  :: PropagationProcessor
    , _times :: TB.Timebounds }
  | NoPropagation
  deriving Show

instance PP.Pretty PropagationProof where
  pretty NoPropagation = PP.text "Nothing to propagate."
  pretty pproof@PropagationProof{} = case _proc pproof of
    TrivialSCCs          -> PP.text "All trivial SCCs of the transition graph admit timebound 1."
    KnowledgePropagation -> PP.text "We propagate bounds from predecessors."

instance T.Processor PropagationProcessor where
  type ProofObject PropagationProcessor = PropagationProof
  type Problem PropagationProcessor     = Its

  solve p prob = return . T.resultToTree p prob $ case solve' prob of
    Nothing                -> T.Fail NoPropagation
    Just (pproof, newprob) -> T.Success (T.Id newprob) pproof (\(T.Id c) -> c)
    where
      solve' = case p of
        TrivialSCCs          -> solveTrivialSCCs
        KnowledgePropagation -> solveKnowledgePropagation


-- trivial sccs
solveTrivialSCCs :: Its -> Maybe (PropagationProof, Its)
solveTrivialSCCs prob
  | null pptimes = Nothing
  | otherwise    = Just (pproof, newprob)
  where
    sccs = TG.trivialSCCs (_tgraph prob)
    pptimes = [(scc,c) | scc <- sccs, scc `notElem` TB.defined (_timebounds prob), let c = one]
    pproof = PropagationProof
      { _proc  = TrivialSCCs
      , _times = M.fromList pptimes }
    newprob = prob {_timebounds = TB.union new old }
      where (old,new) = (_timebounds prob, _times pproof)

boundTrivialSCCs :: T.Strategy Its
boundTrivialSCCs = T.Proc TrivialSCCs

-- FIXME: MS only sound in the non-recursive case
boundTrivialSCCsDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
boundTrivialSCCsDeclaration = T.declare "simp" [desc]  () boundTrivialSCCs
  where desc = "Trivial SCCs in the transition graph admit a timebound 1. This processor always Succeeds."

            
-- kowledge propagation

solveKnowledgePropagation :: Its -> Maybe (PropagationProof, Its)
solveKnowledgePropagation prob = case propagateRules tgraph tbounds rs of
  ([],_)       -> Nothing
  (_,tbounds') -> Just (mkPProof tbounds', prob {_timebounds = tbounds'})
  where
    mkPProof tbounds' = PropagationProof
      { _proc  = KnowledgePropagation
      , _times = M.intersection tbounds' tbounds}
    tbounds = _timebounds prob
    tgraph  = _tgraph prob
    rs      = Gr.topsort tgraph


propagateRules :: TG.TGraph -> TB.Timebounds -> [RuleId] -> ([RuleId],TB.Timebounds)
propagateRules tgraph tbounds = foldl k ([],tbounds)
  where
    k acc@(ps,tbound) r
      | tbound `TB.boundOf` r /= Unknown = acc
      | otherwise = case propagateRule tgraph tbound r of
          Nothing -> acc
          (Just tbound') -> (r:ps,tbound')

propagateRule :: TG.TGraph -> TB.Timebounds -> RuleId -> Maybe TB.Timebounds
propagateRule tgraph tbounds ru
  | ppbound == Unknown = Nothing
  | otherwise          = Just (TB.update ru ppbound tbounds)
  where ppbound = bigAdd [ tbounds `TB.boundOf` t | (t,_) <- TG.predecessors tgraph ru ]


knowledgePropagation :: T.Strategy Its
knowledgePropagation = T.Proc KnowledgePropagation

knowledgePropagationDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
knowledgePropagationDeclaration = T.declare "know" [desc]  () knowledgePropagation
  where desc = "Propagates complexities from the predecessors."


