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

  -- * argument filter
  , argumentFilter
  , unusedFilter
  , argumentFilterDeclaration
  
  -- * Transition Graph
  , unsatPaths
  , unsatPathsDeclaration
  -- ** Unreachable Rules Removal
  , unreachableRules
  , unreachableRulesDeclaration
  -- ** Leaf Rules Removal
  , leafRules
  , leafRulesDeclaration

  -- * 
  , testUnsatRule
  ) where


import           Control.Monad
import           Control.Monad.Trans          (liftIO)
import qualified Data.Graph.Inductive         as Gr
import qualified Data.IntMap.Strict           as IM
import qualified Data.Set                     as S
import qualified Data.Traversable             as F

import qualified Tct.Core.Common.Parser       as CP
import qualified Tct.Core.Common.Pretty       as PP
import qualified Tct.Core.Common.Xml          as Xml
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Data                as T
import qualified Tct.Core.Combinators         as T

import           Tct.Common.ProofCombinators
import qualified Tct.Common.Polynomial        as P
import qualified Tct.Common.SMT as SMT

import           Tct.Its.Data
import           Tct.Its.Data.Complexity
import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds      as TB
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types
import           Tct.Its.Data.Rule


data PropagationProcessor
  = TrivialSCCs -- ^ Trivial SCCs in the transition graph are trivially bounded.
  | KnowledgePropagation
  deriving Show

data PropagationProof
  = PropagationProof
    { pproc_ :: PropagationProcessor
    , times_ :: TB.TimeboundsMap }
  | NoPropagationProof
  deriving Show

instance PP.Pretty PropagationProof where
  pretty NoPropagationProof = PP.text "Nothing to propagate."
  pretty PropagationProof{..} = case pproc_ of
    TrivialSCCs          -> PP.text "All trivial SCCs of the transition graph admit timebound 1."
    KnowledgePropagation -> PP.text "We propagate bounds from predecessors."

instance Xml.Xml PropagationProof where
  toXml NoPropagationProof = Xml.elt "nopropagation" []
  toXml PropagationProof{} = Xml.elt "propagation" []

instance T.Processor PropagationProcessor where
  type ProofObject PropagationProcessor = ApplicationProof PropagationProof
  type I PropagationProcessor           = Its
  type O PropagationProcessor           = Its
  type Forking PropagationProcessor     = T.Optional T.Id

  solve p prob | isClosed prob = return $ closedProof p prob
  solve p prob = return $ case solve' prob of
    Nothing                -> progress p prob NoProgress (Applicable NoPropagationProof)
    Just (pproof, newprob) -> progress p prob (Progress newprob) (Applicable pproof)
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
      , times_ = IM.fromList pptimes }
    newprob = prob {_timebounds = TB.inserts old new }
      where (old,new) = (_timebounds prob, times_ pproof)

boundTrivialSCCs :: ItsStrategy
boundTrivialSCCs = T.Proc TrivialSCCs

-- FIXME: MS only sound in the non-recursive case
boundTrivialSCCsDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
boundTrivialSCCsDeclaration = T.declare "simp" [desc]  () boundTrivialSCCs
  where desc = "Trivial SCCs in the transition graph admit a timebound 1. This processor always Succeeds."


-- kowledge propagation

solveKnowledgePropagation :: Its -> Maybe (PropagationProof, Its)
solveKnowledgePropagation prob = case propagateRules tgraph tbounds rs of
  ([],_)       -> Nothing
  (ris,tbounds') -> Just (mkPProof ris tbounds', prob {_timebounds = tbounds'})
  where
    mkPProof ris tbounds' = PropagationProof
      { pproc_ = KnowledgePropagation
      , times_ = IM.fromList $ map (\ri -> (ri,tbounds' `TB.tboundOf` ri)) ris }
    tbounds = _timebounds prob
    tgraph  = _tgraph prob
    rs      = Gr.topsort tgraph

propagateRules :: TG.TGraph -> TB.Timebounds -> [RuleId] -> ([RuleId],TB.Timebounds)
propagateRules tgraph tbounds = foldl k ([],tbounds)
  where
    k acc@(ps,tbound) r
      | tbound `TB.tboundOf` r /= Unknown = acc
      | otherwise = case propagateRule tgraph tbound r of
          Nothing -> acc
          (Just tbound') -> (r:ps,tbound')

propagateRule :: TG.TGraph -> TB.Timebounds -> RuleId -> Maybe TB.Timebounds
propagateRule tgraph tbounds ru
  | ppbound == Unknown = Nothing
  | otherwise          = Just (TB.update ru ppbound tbounds)
  where ppbound = bigAdd [ tbounds `TB.tboundOf` t | (t,_) <- TG.predecessors tgraph ru ]


knowledgePropagation :: ItsStrategy
knowledgePropagation = T.Proc KnowledgePropagation

knowledgePropagationDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
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

instance Xml.Xml RuleRemovalProof where
  toXml NoRuleRemovalProof{} = Xml.elt "noruleremoval" []
  toXml RuleRemovalProof{}   = Xml.elt "ruleremoval" []
 
-- * Rechability

instance T.Processor RuleRemovalProcessor where
  type ProofObject RuleRemovalProcessor = ApplicationProof RuleRemovalProof
  type I RuleRemovalProcessor           = Its
  type O RuleRemovalProcessor           = Its
  type Forking RuleRemovalProcessor     = T.Optional T.Id

  solve p prob | isClosed prob = return $ closedProof p prob
  solve UnsatRules prob        = solveUnsatRules prob
  solve UnreachableRules prob  = return $ solveUnreachableRules prob
  solve LeafRules prob         = return $ solveLeafRules prob

solveUnsatRules :: Its -> T.TctM (T.Return (T.ProofTree Its))
solveUnsatRules prob = do
  unsats <- liftIO $ do
    res <- F.sequence $ IM.map testUnsatRule nrules
    return . IM.keys $ IM.filter id res
  return $ if null unsats
    then progress p prob NoProgress (Applicable (NoRuleRemovalProof p))
    else progress p prob (Progress $ removeRules unsats prob) (Applicable (RuleRemovalProof p unsats))
  where
    p = UnsatRules
    nrules     = IM.filterWithKey (\k _ -> k `elem` nonDefined) (_irules prob)
    nonDefined = TB.nonDefined (_timebounds prob)

testUnsatRule :: Rule -> IO Bool
testUnsatRule r = do
  s :: SMT.Result () <- SMT.smtSolveSt SMT.yices $ do
    SMT.setLogic SMT.QF_LIA
    SMT.assert $ SMT.bigAnd (map encodeAtom (con r))
    return $ SMT.decode ()
  return (SMT.isUnsat s)

solveUnreachableRules :: Its -> T.Return (T.ProofTree Its)
solveUnreachableRules prob =
  let unreachable = Gr.nodes tgraph `minus` Gr.dfs starts tgraph in
  if null unreachable
    then progress p prob NoProgress (Applicable (NoRuleRemovalProof p))
    else progress p prob (Progress $ removeRules unreachable prob) (Applicable (RuleRemovalProof p unreachable))
  where
    p         = UnreachableRules
    tgraph    = _tgraph prob
    starts    = IM.keys (startrules prob)
    minus a b = S.toList $ S.fromList a `S.difference` S.fromList b

solveLeafRules :: Its -> T.Return (T.ProofTree Its)
solveLeafRules prob =
  let leafs = solveLeafRule (_tgraph prob) [] in
  if null leafs
    then progress p prob NoProgress (Applicable (NoRuleRemovalProof p))
    else progress p prob (Progress $ mkproof leafs) (Applicable (RuleRemovalProof p leafs))
  where
    mkproof leafs = let prob' = removeRules leafs prob in prob'{_timebounds = TB.addLeafCost (_timebounds prob') (length leafs)}
    p         = LeafRules
    isLeave gr n = Gr.indeg gr n > 0 && Gr.outdeg gr n == 0
    solveLeafRule gr leafs =
      let leafs' = filter (isLeave gr)  (Gr.nodes gr) in
      if null leafs'
        then leafs
        else solveLeafRule (Gr.delNodes leafs' gr) (leafs' ++ leafs)

-- * unsat path removal
data PathRemovalProcessor = UnsatPaths
  deriving Show

data PathRemovalProof
  = PathRemovalProof [(RuleId, RuleId)]
  | NoPathRemovalProof
  deriving Show

instance PP.Pretty PathRemovalProof where
  pretty NoPathRemovalProof    = PP.text "Nothing happend"
  pretty (PathRemovalProof es) = PP.text "We remove following edges from the transition graph: " PP.<> PP.pretty es

instance Xml.Xml PathRemovalProof where
  toXml NoPathRemovalProof   = Xml.elt "nopathremoval" []
  toXml (PathRemovalProof _) = Xml.elt "pathremoval" []

instance T.Processor PathRemovalProcessor where
  type ProofObject PathRemovalProcessor = ApplicationProof PathRemovalProof
  type I PathRemovalProcessor           = Its
  type O PathRemovalProcessor           = Its
  type Forking PathRemovalProcessor     = T.Optional T.Id

  solve p prob | isClosed prob = return $ closedProof p prob
  solve UnsatPaths prob        = solveUnsatPaths prob

solveUnsatPaths :: Its -> T.TctM (T.Return (T.ProofTree Its))
solveUnsatPaths prob = do
  unsats <- liftIO $ filterM solveUnsatPath (Gr.edges tgraph)
  return $ if null unsats
    then progress p prob NoProgress (Applicable NoPathRemovalProof)
    else progress p prob (Progress (mkprob unsats)) (Applicable (PathRemovalProof unsats))
  where
    p = UnsatPaths
    tgraph = _tgraph prob
    irules = _irules prob

    mkprob es = prob {_tgraph = Gr.delEdges es tgraph}
    solveUnsatPath (n1,n2) = case chain (irules IM.! n1) (irules IM.! n2) of
      Nothing -> return False
      Just r  -> testUnsatRule r


-- * argument filtering

data ArgumentFilterProcessor = ArgumentFilter [Int] -- against the convention: lists indices to remove
  deriving Show

data ArgumentFilterProof
  = ArgumentFilterProof [Int]
  | NoArgumentFilterProof
  deriving Show

instance PP.Pretty ArgumentFilterProof where
  pretty NoArgumentFilterProof    = PP.text "Nothing happend"
  pretty (ArgumentFilterProof es) = PP.text "We remove following argument positions: " PP.<> PP.pretty es PP.<> PP.dot

instance Xml.Xml ArgumentFilterProof where
  toXml NoArgumentFilterProof   = Xml.elt "noargumentfilter" []
  toXml (ArgumentFilterProof _) = Xml.elt "argumentfilter" []


instance T.Processor ArgumentFilterProcessor where
  type ProofObject ArgumentFilterProcessor = ApplicationProof ArgumentFilterProof
  type I ArgumentFilterProcessor           = Its
  type O ArgumentFilterProcessor           = Its
  type Forking ArgumentFilterProcessor     = T.Optional T.Id

  solve p prob | isClosed prob = return $ closedProof p prob
  solve p prob        = return $ solveArgumentFilter prob p

solveArgumentFilter :: Its -> ArgumentFilterProcessor -> T.Return (T.ProofTree Its)
solveArgumentFilter prob p@(ArgumentFilter as)
  | null as   = progress p prob NoProgress (Applicable NoArgumentFilterProof)
  | otherwise = progress p prob (Progress nprob) (Applicable (ArgumentFilterProof as))
  where
    nprob = prob
      { _irules          = IM.map afOnRule (_irules prob)
      , _startterm       = afOnTerm (_startterm prob)
      , _rvgraph         = Nothing
      , _sizebounds      = Nothing
      , _localSizebounds = Nothing }
    afOnRule (Rule l r cs) = Rule (afOnTerm l) (map afOnTerm r) cs
    afOnTerm (Term fs ars) = Term fs (fst . unzip . filter ((`notElem` as) . snd) $ zip ars [0..])

-- select positions not occuring in constraints
unusedFilter :: Its -> [Int]
unusedFilter prob = indices $ foldr (S.union . unusedR) S.empty allrules
  where
    allrules = IM.elems (_irules prob)
    indices vs = fst . unzip . filter ((`S.member` unused) . snd) $ zip [0..] (domain prob)
      where unused = S.fromList (domain prob) `S.difference` vs
    unusedR r = foldr (S.union . S.fromList . P.variables) S.empty (celems $ con r)


-- * instances
unsatRules :: ItsStrategy
unsatRules = T.Proc UnsatRules

unsatRulesDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
unsatRulesDeclaration = T.declare "unsatRules" [desc]  () unsatRules
  where desc = "This processor removes rules with unsatisfiable constraints."

unsatPaths :: ItsStrategy
unsatPaths = T.Proc UnsatPaths

unsatPathsDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
unsatPathsDeclaration = T.declare "unsatPaths" [desc]  () unsatPaths
  where desc = "This processor tests wether rule2 can follow rule1 for all edges in the flow graph."

unreachableRules :: ItsStrategy
unreachableRules = T.Proc UnreachableRules

unreachableRulesDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
unreachableRulesDeclaration = T.declare "unreachableRules" [desc]  () unreachableRules
  where desc = "This processor removes rules not reachable from the starting location."

leafRules :: ItsStrategy
leafRules = T.Proc LeafRules

leafRulesDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
leafRulesDeclaration = T.declare "leafRules" [desc]  () leafRules
  where desc = "This processor removes leafs in the transition graph."

argumentFilter :: [Int] -> ItsStrategy
argumentFilter = T.Proc . ArgumentFilter

argumentFilterDeclaration :: T.Declaration ('[T.Argument 'T.Optional Filter] T.:-> ItsStrategy)
argumentFilterDeclaration = T.declare "argumentFilter" [desc] (T.OneTuple $ arg) argumentFilter'
  where
    desc = "Removes argument positions acoording to the provided argument."
    arg = filterArg `T.optional` Unused
    argumentFilter' = const $ T.withProblem (argumentFilter . unusedFilter)

data Filter 
  = Unused 
  deriving Show

filterArg :: T.Argument T.Required Filter
filterArg = T.arg { T.argName = "filter" , T.argDomain = "<filter>" }  `T.withHelp` (f1:filters)
  where
    f1      = "Specifies the filter to apply. <filter> is one of:"
    filters = map ("* "++)  [ show Unused ]

instance T.SParsable i i Filter where
  parseS = CP.choice
    [ CP.symbol (show Unused) >> return Unused ]

