{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tct.Its.Processor.Simplification
  (
  -- * Trivial SCCs
  boundTrivialSCCs
  , boundTrivialSCCsDeclaration

  -- * Knowledge Propagation
  , knowledgePropagation
  , knowledgePropagationDeclaration

  -- * Unsat Rules Removal
  , unsatRules
  , unsatRulesDeclaration
  
  -- * Transition Graph
  -- ** Unreachable Rules Removal
  , unreachableRules
  , unreachableRulesDeclaration
  -- ** Leaf Rules Removal
  , leafRules
  , leafRulesDeclaration
  ) where


import           Control.Monad.Trans          (liftIO)
import qualified Data.Graph.Inductive         as Gr
import qualified Data.IntMap.Strict           as IM
import qualified Data.Map.Strict              as M
import qualified Data.Set                     as S
import qualified Data.Traversable             as F

import qualified SLogic.Smt                   as SMT

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Data                as T
import qualified Tct.Core.Combinators         as T

import qualified Tct.Common.Polynomial        as P

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
    { pproc_ :: PropagationProcessor
    , times_ :: TB.Timebounds }
  | NoPropagation
  deriving Show

instance PP.Pretty PropagationProof where
  pretty NoPropagation = PP.text "Nothing to propagate."
  pretty PropagationProof{..} = case pproc_ of
    TrivialSCCs          -> PP.text "All trivial SCCs of the transition graph admit timebound 1."
    KnowledgePropagation -> PP.text "We propagate bounds from predecessors."

instance T.Processor PropagationProcessor where
  type ProofObject PropagationProcessor = PropagationProof
  type Problem PropagationProcessor     = Its

  solve p prob = return $ case solve' prob of
    Nothing                -> progress p prob NoProgress NoPropagation
    Just (pproof, newprob) -> progress p prob (Progress newprob) pproof
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
      { pproc_ = TrivialSCCs
      , times_ = M.fromList pptimes }
    newprob = prob {_timebounds = TB.union new old }
      where (old,new) = (_timebounds prob, times_ pproof)

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
      { pproc_ = KnowledgePropagation
      , times_ = M.intersection tbounds' tbounds}
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

-- * Rule Removal

data RuleRemovalProcessor
  = UnsatRules
  | UnreachableRules
  | LeafRules
  deriving (Show)

data RuleRemovalProof
  = RuleRemovalProof
    { rproc_  :: RuleRemovalProcessor
    , rrules_ :: [RuleId]}
  | NoRuleRemovalProof
    { rproc_ :: RuleRemovalProcessor }
  deriving Show

instance PP.Pretty RuleRemovalProof where
  pretty RuleRemovalProof{..} =
    case rproc_ of
      UnsatRules       ->
        PP.text "Following transitions have unsatisfiable constraints and are removed: " PP.<+> PP.pretty rrules_
      UnreachableRules ->
        PP.text "Following transitions are not reachable from the starting states and are revomed:" PP.<+> PP.pretty rrules_
      LeafRules ->
        PP.text "Following transitions are estimated by its predecessors and are removed" PP.<+> PP.pretty rrules_
  pretty NoRuleRemovalProof{..} =
    case rproc_ of
      UnsatRules       -> PP.text "No constraint could have been show to be unsatisfiable. No rules are removed."
      UnreachableRules -> PP.text "All transitions are reachable from the starting states. No rules are removed."
      LeafRules        -> PP.text "No leaf rules. No rules are removed."
-- * Rechability

instance T.Processor RuleRemovalProcessor where
  type ProofObject RuleRemovalProcessor = RuleRemovalProof
  type Problem RuleRemovalProcessor     = Its

  solve UnsatRules prob       = solveUnsatRules prob
  solve UnreachableRules prob = return $ solveUnreachableRules prob
  solve LeafRules prob        = return $ solveLeafRules prob

removeRules :: [RuleId] -> Its -> Its
removeRules irs prob = prob 
  { _irules          = IM.filterWithKey (\k _ -> k `notElem` irs) (_irules prob)
  , _startrules      = IM.filterWithKey (\k _ -> k `notElem` irs) (_startrules prob)
  , _tgraph          = Gr.delNodes irs (_tgraph prob)
  -- MS: TODO filter wrt to labels
  , _rvgraph         = Nothing
  , _timebounds      = M.filterWithKey (\k _ -> k `notElem` irs) (_timebounds prob)
  , _sizebounds      = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` _sizebounds prob
  , _localSizebounds = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` _localSizebounds prob }

solveUnsatRules :: Its -> T.TctM (T.Return (T.ProofTree Its))
solveUnsatRules prob = do
  unsats <- liftIO $ do
      res <- F.sequence $ IM.map entscheide allrules
      return $ IM.keys $ IM.filter isUnsat res
  return $ if null unsats
    then progress p prob NoProgress (NoRuleRemovalProof p)
    else progress p prob (Progress $ removeRules unsats prob) (RuleRemovalProof p unsats)
  where
    p = UnsatRules
    allrules = _irules prob
    isUnsat r = case r of
      SMT.Unsat -> True
      _         -> False
    entscheide :: Rule -> IO (SMT.Result ())
    entscheide r =
      SMT.solveStM SMT.yices $ do
        SMT.setFormat "QF_LIA"
        SMT.assert $ SMT.bigAnd (map encodeAtom (con r))
        return $ SMT.decode ()
      where
        encodeAtom (Eq p1 p2)  = encodePoly p1 SMT..== encodePoly p2
        encodeAtom (Gte p1 p2) = encodePoly p1 SMT..>= encodePoly p2
        encodePoly ms     = SMT.bigAdd (map encodeMono $ P.toView' ms)
        encodeMono (c,ps) = SMT.bigMul (SMT.num c: concatMap encodePower ps)
        encodePower (v,e) = replicate e (SMT.IVar SMT.tInt v)

solveUnreachableRules :: Its -> T.Return (T.ProofTree Its)
solveUnreachableRules prob =
  let unreachable = Gr.nodes tgraph `minus` Gr.dfs starts tgraph in
  if null unreachable
    then progress p prob NoProgress (NoRuleRemovalProof p)
    else progress p prob (Progress $ removeRules unreachable prob) (RuleRemovalProof p unreachable)
  where
    p         = UnreachableRules
    tgraph    = _tgraph prob
    starts    = IM.keys $ _startrules prob
    minus a b = S.toList $ S.fromList a `S.difference` S.fromList b

solveLeafRules :: Its -> T.Return (T.ProofTree Its)
solveLeafRules prob =
  let leafs = solveLeafRule (_tgraph prob) [] in
  if null leafs
    then progress p prob NoProgress (NoRuleRemovalProof p)
    else progress p prob (Progress $ removeRules leafs prob) (RuleRemovalProof p leafs)
  where
    p         = LeafRules
    isLeave gr n = Gr.outdeg gr n == 0
    solveLeafRule gr leafs =
      let leafs' = filter (isLeave gr)  (Gr.nodes gr) in
      if null leafs'
        then leafs
        else solveLeafRule (Gr.delNodes leafs' gr) (leafs' ++ leafs)


unsatRules :: T.Strategy Its
unsatRules = T.Proc UnsatRules

unsatRulesDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
unsatRulesDeclaration = T.declare "unsatRules" [desc]  () unsatRules
  where desc = "This processor removes rules with unsatisfiable constraints."

unreachableRules :: T.Strategy Its
unreachableRules = T.Proc UnreachableRules

unreachableRulesDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
unreachableRulesDeclaration = T.declare "unreachableRules" [desc]  () unsatRules
  where desc = "This processor removes rules not reachable from the starting state."

leafRules :: T.Strategy Its
leafRules = T.Proc LeafRules

leafRulesDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
leafRulesDeclaration = T.declare "leafRules" [desc]  () unsatRules
  where desc = "This processor removes leafs in the transition graph."

