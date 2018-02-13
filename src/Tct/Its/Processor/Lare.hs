{- |
This module provides a feasibility check using LARE.

More pricesly this module implements:

  * an abstraction from ITS to LARE, and
  * a wrapper for the LARE library.

-}
{-# LANGUAGE RecordWildCards, StandaloneDeriving #-}
module Tct.Its.Processor.Lare where


import           Data.Foldable                (toList)
import qualified Data.IntMap.Strict           as IM
import           Data.List                    (intersperse, (\\))
import           Data.Monoid                  ((<>))
import qualified Data.Set                     as S
import           Data.Either                       (either)

import           Tct.Core.Common.Pretty       (Pretty, pretty)
import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.Xml          (Xml, toXml)
import qualified Tct.Core.Common.Xml          as Xml
import           Tct.Core.Data                (processor, (.>>>))
import qualified Tct.Core.Data                as T

import qualified Tct.Common.Polynomial        as P

import           Tct.Its.Data.Complexity      (Complexity (..))
import qualified Tct.Its.Data.LocalSizebounds as LB (compute, lboundOf)
import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds      as TB (initialise)
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types
import qualified Tct.Its.Processor.Looptree   as LT

import qualified Lare.Analysis as LA
import qualified Lare.Flow as LA
import qualified Lare.Tick as LA


type Edge l    = LA.Edge (LA.Vtx Fun) (l (LA.Var Var))
data Program l = Program
  { dom :: [LA.Var Var]
  , cfg :: LA.Program Fun (l (LA.Var Var)) }
type Proof     = LA.Tree [Edge LA.F]
type SizeAbstraction = Program LA.Assignment
type FlowAbstraction = Program LA.F

deriving instance Show (Program LA.Assignment)
deriving instance Show (Program LA.F)

-- Size Abstraction of the ITS
-- Replaces constraints of each edge of the CFG with its local growh.
toEdges :: Its -> IM.IntMap (Edge LA.Assignment)
toEdges prob = flip IM.mapWithKey (irules_ prob) $
  \i Rule{..} ->
    LA.edge
      (LA.V $ fun lhs)
      (LA.Assignment
        [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- domain prob, let rv = RV i 0 v ])
      (LA.V $ fun $ head rhs)
  where Just lsb = localSizebounds_ prob

toBound :: Complexity -> LA.Bound (LA.Var Var)
toBound Unknown   = LA.Unknown
toBound (NPoly p) = foldr k (LA.Sum []) (P.toView p) where
  k (c,[])      (LA.Sum bs) = LA.Sum $ (c, LA.K):bs
  k (c,[(v,i)]) (LA.Sum bs)
    | i == 1                = LA.Sum $ (c, LA.Var v):bs
  k _ _                     = LA.Unknown


-- Transforms the ITS and coputed loop structure to the intermediate represenation of the LARE library.
toLare :: Its -> LT.Top [RuleId] -> Program LA.Assignment
toLare prob lt =
  let
    lare = go0 lt
    vs1  = [ LA.Var v | v <- domain prob ]
    vs2  = [ LA.Ann v | l <- toList lare, let LA.Assignment [ (LA.Ann v,_) ] = LA.loopid l ]
  in
  Program (vs1++vs2) lare

  where
  lbs   = toEdges prob
  edges = IM.elems lbs
  from  = fmap (lbs IM.!)

  go0 (LT.Top es ts)    = LA.Top (from es) (goN `fmap` zip (positions [0]) ts)
  goN (pos,LT.Tree{..}) = LA.Tree (loop edges (from program) pos bound) (goN `fmap` zip (positions pos) subprograms)

  loop cfg cfg' pos bnd = LA.Loop
    { LA.program = cfg'
    , LA.loopid  = LA.Assignment [(LA.Ann (posToVar pos), toBound bnd)]
    , LA.inflow  = snub [ LA.src e1 | e1 <- cfg', e2 <- cfg \\ cfg', LA.dst e2 == LA.src e1 ]
    , LA.outflow = snub [ LA.dst e1 | e1 <- cfg', e2 <- cfg \\ cfg', LA.dst e1 == LA.src e2 ]
    , LA.outer   = LA.nodes cfg `intersect` LA.nodes cfg' }
    where
      posToVar = intersperse '.' . concat . fmap show . reverse
      intersect a b = S.toList $ S.fromList a `S.intersection` S.fromList b


  positions pos = (:pos) `fmap` iterate succ (0 :: Int)


toLareM :: Its -> LT.Top [RuleId] -> T.TctM (Program LA.Assignment)
toLareM prob lt = case localSizebounds_ prob of
  Just _  -> return $ toLare prob lt
  Nothing -> do
    lb <- LB.compute (domain prob) (irules_ prob)
    return $ toLare (prob { localSizebounds_ = Just lb }) lt

-- add sinks

addSinks :: Its -> Its
addSinks prob = prob
  { irules_          = allrules
  , tgraph_          = TG.estimateGraph allrules
  , rvgraph_         = Nothing
  , timebounds_      =
      TB.initialise
        (IM.keys allrules)
        (IM.keys $ IM.filter (\r -> fun (lhs r) == fun (startterm_ prob) ) allrules)
  , sizebounds_      = Nothing
  , localSizebounds_ = Nothing }

  where
  allrules = irules `IM.union` sinks

  irules = irules_ prob
  term f = Term { fun = f, args = args (startterm_ prob) }
  rule f = Rule { lhs = term f, rhs = [ term "exitus616"], con = [] }

  sinks = IM.fromList $
    zip
     [ succ (fst (IM.findMax irules)) ..]
     [ rule f |  f <- nub [ fun (lhs r) | n <- needSinks, let r = irules IM.! n ] ]
  nub = S.toList . S.fromList



  needSinks =
    concat
      [ theSCC scc
        | ps <- TG.rootsPaths (tgraph_ prob)
        , let scc = (head $ reverse ps)
        , isNonTrivial scc ]

  isNonTrivial (NonTrivial _) = True
  isNonTrivial _              = False

--- * Processors -----------------------------------------------------------------------------------------------------

-- FIXME: use Tct.Core.Transform

data AddSinksProcessor = AddSinks deriving Show

instance T.Processor AddSinksProcessor where
  type ProofObject AddSinksProcessor = ()
  type In AddSinksProcessor          = Its
  type Out AddSinksProcessor         = Its
  type Forking AddSinksProcessor     = T.Id

  execute AddSinks prob = T.succeedWithId () (addSinks prob)


data LooptreeTransformer = LooptreeTransformer deriving Show

instance T.Processor LooptreeTransformer where
  type ProofObject LooptreeTransformer = LT.LooptreeProof
  type In LooptreeTransformer          = Its
  type Out LooptreeTransformer         = (Its, LT.LooptreeProof)
  type Forking LooptreeTransformer     = T.Id

  execute LooptreeTransformer prob = do
    tree <- LT.infer prob
    let proof = LT.LooptreeProof tree
    if LT.isComplete tree
      then T.succeedWithId proof (prob,proof)
      else T.abortWith proof


data SizeAbstractionProcessor = SizeAbstraction deriving Show

instance T.Processor SizeAbstractionProcessor where
  type ProofObject SizeAbstractionProcessor = ()
  type In SizeAbstractionProcessor          = (Its, LT.LooptreeProof)
  type Out SizeAbstractionProcessor         = SizeAbstraction
  type Forking SizeAbstractionProcessor     = T.Id

  execute SizeAbstraction (prob, LT.LooptreeProof tree) = T.succeedWithId () =<< toLareM prob tree


data FlowAbstractionProcessor = FlowAbstraction deriving Show

instance T.Processor FlowAbstractionProcessor where
  type ProofObject FlowAbstractionProcessor = ()
  type In FlowAbstractionProcessor          = SizeAbstraction
  type Out FlowAbstractionProcessor         = FlowAbstraction
  type Forking FlowAbstractionProcessor     = T.Id

  execute FlowAbstraction (Program vs prob) = T.succeedWithId () $ Program vs' (LA.toFlow vs' prob)
    where vs' = LA.Counter: LA.Huge : LA.K : vs

data LareProcessor = LareProcessor deriving Show
data LareProof = LareProof Proof deriving Show

instance T.Processor LareProcessor where
  type ProofObject LareProcessor = LareProof
  type In LareProcessor          = FlowAbstraction
  type Out LareProcessor         = ()
  type Forking LareProcessor     = T.Judgement

  execute LareProcessor (Program vs prob) =
    let
      proofM = LA.convertWith (LA.ticked $ LA.flow vs) prob
    in
    either
      (T.abortWith)
      (\proof -> T.succeedWith0 (LareProof proof) (T.judgement $ T.timeUBCert $ toComplexity $ LA.boundOfProof proof))
      proofM


toComplexity :: LA.Complexity -> T.Complexity
toComplexity LA.Indefinite = T.Unknown
toComplexity LA.Constant   = T.Poly (Just 0)
toComplexity LA.Linear     = T.Poly (Just 1)
toComplexity LA.Polynomial = T.Poly Nothing
toComplexity LA.Primrec    = T.Primrec


--- * Util -----------------------------------------------------------------------------------------------------------

snub = S.toList . S.fromList

--- * Pretty ---------------------------------------------------------------------------------------------------------

instance Xml.Xml (Its,LT.LooptreeProof) where toXml = const Xml.empty
instance Xml.Xml (a,Program l) where toXml = const Xml.empty
instance Xml.Xml (Program l) where toXml = const Xml.empty

instance Pretty LareProof where pretty (LareProof p) = pretty p
instance Xml LareProof where toXml = const Xml.empty

instance Pretty (Program LA.Assignment) where pretty p = ppProgram pretty p
instance Pretty (Program LA.F) where pretty p = ppProgram pretty p

ppProgram :: (LA.Program Fun (t (LA.Var Var)) -> PP.Doc) -> Program t -> PP.Doc
ppProgram k (Program vs p) = PP.vcat
  [ PP.text "Program:"
  , PP.indent 2 $ PP.text "Domain: " <> PP.pretty vs
  , PP.indent 2 $ PP.align $ k p ]


