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

import           Tct.Core.Common.Pretty       (Pretty, pretty)
import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.Xml          (Xml, toXml)
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import qualified Tct.Common.Polynomial        as P

import           Tct.Its.Data.Complexity
import qualified Tct.Its.Data.LocalSizebounds as LB (compute, lboundOf)
import           Tct.Its.Data.Problem
import           Tct.Its.Data.Types
import qualified Tct.Its.Processor.Looptree   as LT

import qualified Lare.Analysis                as LA
import qualified Lare.Flow                    as LA


type Edge l    = LA.Edge (LA.V Fun) (l (LA.Var Var))
data Program l = Program
  { dom :: [LA.Var Var]
  , cfg :: LA.Program (LA.V Fun) (l (LA.Var Var)) }
type Proof     = LA.Top [Edge LA.F] [Edge LA.F]

deriving instance Show (Program LA.Assignment)
deriving instance Show (Program LA.F)

-- Size Abstraction of the ITS
-- Replaces constraints of each edge of the CFG with its local growh.
toEdges :: Its -> IM.IntMap (Edge LA.Assignment)
toEdges prob = flip IM.mapWithKey irs $
  \i Rule{..} ->
    LA.edge
      (LA.V $ fun lhs)
      (LA.Assignment [ (LA.Var v, toBound $ LB.lboundOf lsb rv) | v <- vs, let rv = RV i 1 v ])
      (LA.V $ fun $ head rhs)
  where
    irs      = irules_ prob
    vs       = domain prob
    Just lsb = localSizebounds_ prob

toBound :: Complexity -> LA.Bound (LA.Var Var)
toBound Unknown    = LA.Unknown
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
    , LA.outer   = [ LA.Out v | e1 <- cfg', e2 <- cfg \\ cfg', LA.src e1 == LA.dst e2, let LA.V v = LA.src e1 ] }
    where  posToVar = intersperse '.' . concat . fmap show . reverse

  positions pos = (:pos) `fmap` iterate succ 0


toLareM :: Its -> LT.Top [RuleId] -> T.TctM (Program LA.Assignment)
toLareM prob lt = case localSizebounds_ prob of
  Just _  -> return $ toLare prob lt
  Nothing -> do
    lb <- LB.compute (domain prob) (irules_ prob)
    return $ toLare (prob { localSizebounds_ = Just lb }) lt



--- * Processors -----------------------------------------------------------------------------------------------------


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


data SizeAbstraction = SizeAbstraction deriving Show

instance T.Processor SizeAbstraction where
  type ProofObject SizeAbstraction = ()
  type In SizeAbstraction          = (Its, LT.LooptreeProof)
  type Out SizeAbstraction         = Program LA.Assignment
  type Forking SizeAbstraction     = T.Id

  execute SizeAbstraction (prob, LT.LooptreeProof tree) = T.succeedWithId () =<< toLareM prob tree


data FlowAbstraction = FlowAbstraction deriving Show

instance T.Processor FlowAbstraction where
  type ProofObject FlowAbstraction = ()
  type In FlowAbstraction          = Program LA.Assignment
  type Out FlowAbstraction         = Program LA.F
  type Forking FlowAbstraction     = T.Id

  execute FlowAbstraction (Program vs prob) = T.succeedWithId () $ Program vs' (LA.toFlow0 vs' prob)
    where vs' = LA.Counter: LA.Huge : LA.K : vs

data LareProcessor = LareProcessor deriving Show
data LareProof = LareProof Proof deriving Show

instance T.Processor LareProcessor where
  type ProofObject LareProcessor = LareProof
  type In LareProcessor          = Program LA.F
  type Out LareProcessor         = ()
  type Forking LareProcessor     = T.Judgement

  execute LareProcessor (Program vs prob) =
    let
      proof = LA.convert (LA.flow vs) prob
      -- TODO: bound
    in
    T.succeedWith0 (LareProof proof) (T.judgement $ T.timeUBCert T.Primrec)


--- * Pretty ---------------------------------------------------------------------------------------------------------

instance Xml.Xml (Its,LT.LooptreeProof) where toXml = const Xml.empty
instance Xml.Xml (a,Program l) where toXml = const Xml.empty
instance Xml.Xml (Program l) where toXml = const Xml.empty

instance Pretty LareProof where pretty (LareProof p) = pretty p
instance Xml LareProof where toXml = const Xml.empty

instance Pretty (Program LA.Assignment) where pretty p = ppProgram pretty p
instance Pretty (Program LA.F) where pretty p = ppProgram pretty p

ppProgram :: (LA.Program (LA.V Fun) (t (LA.Var Var)) -> PP.Doc) -> Program t -> PP.Doc
ppProgram k (Program vs p) = PP.vcat
  [ PP.text "Program:"
  , PP.indent 2 $ PP.text "Domain: " <> PP.pretty vs
  , PP.indent 2 $ PP.align $ k p ]


