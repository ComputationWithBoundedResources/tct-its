module Tct.Its.Data.Problem
  ( Its (..)

  , validate
  , initialiseSizebounds
  , computeSizebounds
  , computeLocalSizebounds

  --, rvss
  , domain
  , closed
  , updateTimebounds

  , itsMode
  ) where


import           Control.Monad                    (void)
import           Control.Monad.Trans              (liftIO)
import qualified Data.Foldable                    as F (toList)
import qualified Data.Graph.Inductive.Dot         as Gr
import qualified Data.Map                         as M
import           Data.Maybe                       (fromJust)

import           Tct.Core.Common.Error            (TctError (..))
import qualified Tct.Core.Common.Parser           as PR
import qualified Tct.Core.Common.Pretty           as PP
import           Tct.Core.Data
import           Tct.Core.Main                    (TctMode (..), unit)
import           Tct.Core.Processor.Trivial       (failing)

import qualified Tct.Common.Polynomial            as P

import           Tct.Its.Data.Cost
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds     as LB (compute)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import qualified Tct.Its.Data.ResultVariableGraph as RVG (compute)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
import qualified Tct.Its.Data.Sizebounds          as SB (initialise, updateSizebounds)
import           Tct.Its.Data.Timebounds          (Timebounds)
import qualified Tct.Its.Data.Timebounds          as TB
import           Tct.Its.Data.TransitionGraph     (TGraph, estimateGraph, initialRules)
import           Tct.Its.Data.Types


data Its = Its
  { _irules          :: Rules
  , _signature       :: Signature
  , _startterm       :: Term

  , _tgraph          :: TGraph
  , _rvgraph         :: Maybe RVGraph

  , _timebounds      :: Timebounds
  , _sizebounds      :: Maybe Sizebounds
  , _localSizebounds :: Maybe LocalSizebounds
  } deriving Show



initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],vs, rsl) = Its
  { _irules          = irules
  , _signature       = mkSignature

  , _startterm       = Term fs (map P.variable vs)
  , _tgraph          = tgraph
  , _rvgraph         = Nothing

  , _timebounds      = TB.initialise ris (initialRules tgraph)
  , _sizebounds      = Nothing
  , _localSizebounds = Nothing }
  where
    tgraph = estimateGraph irules
    irules = zip [0..] rsl
    ris = fst (unzip irules)
    mkSignature = foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rsl ]
      where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"


-- | Sets localSizebounds, rvgraph, sizebounds if not already defined.
initialiseSizebounds :: Its -> IO Its
initialiseSizebounds prob = case _localSizebounds prob of
  Just _ ->  return prob
  Nothing -> newprob
  where
    newprob = do
      lbounds <- LB.compute (domain prob) (_irules prob)
      let
        rvgraph = RVG.compute (_tgraph prob) lbounds
        sbounds = SB.initialise lbounds
      liftIO $ writeFile "/tmp/rvgraph.dot" $ maybe "Gr" (Gr.showDot . Gr.fglToDot) (_rvgraph prob)
      return $ prob {_localSizebounds = Just lbounds, _rvgraph = Just rvgraph, _sizebounds = Just sbounds}

data LocalSizeboundsProcessor = LocalSizeboundsProc deriving Show

data LocalSizeboundsProof = LocalSizeboundsProof (Vars, LocalSizebounds) RVGraph
  deriving Show

instance PP.Pretty LocalSizeboundsProof where
  pretty (LocalSizeboundsProof vlbounds _) = 
    PP.text "LocalSizebounds generated; rvgraph"
    PP.<$$> PP.indent 2 (PP.pretty vlbounds)

instance Processor LocalSizeboundsProcessor where
  type ProofObject LocalSizeboundsProcessor = LocalSizeboundsProof
  type Problem LocalSizeboundsProcessor     = Its
  solve p prob = do
    nprob <- liftIO $ initialiseSizebounds prob
    let pproof = LocalSizeboundsProof (domain prob, fromJust $ _localSizebounds nprob) (fromJust $ _rvgraph nprob)
    return $ resultToTree p prob $ Success (Id nprob) pproof (\(Id c) -> c)

computeLocalSizebounds :: Strategy Its
computeLocalSizebounds = Proc LocalSizeboundsProc

computeSizebounds :: Strategy Its
computeSizebounds = Proc SizeboundsProc

data SizeboundsProcessor = SizeboundsProc deriving Show

data SizeboundsProof = SizeboundsProof deriving Show

instance PP.Pretty SizeboundsProof where
  pretty = const (PP.text "Sizebounds computed.")

instance Processor SizeboundsProcessor where
  type ProofObject SizeboundsProcessor = SizeboundsProof
  type Problem SizeboundsProcessor     = Its
  solve p prob = return $ resultToTree p prob $ Success (Id nprob) SizeboundsProof (\(Id c) -> c)
    where nprob = updateSizebounds prob

updateSizebounds :: Its -> Its
updateSizebounds prob = prob {_sizebounds = Just sbounds'} where
  sbounds' = SB.updateSizebounds 
    (_tgraph prob) 
    (fromJust $ _rvgraph prob) 
    (_timebounds prob) 
    (fromJust $ _sizebounds prob)  
    (fromJust $ _localSizebounds prob)
  

validate :: Rules -> Bool
validate = const True

{-rvss :: Vars -> Rules -> [RV]-}
{-rvss vs = concatMap k-}
  {-where k (i,r) = [ (i, rhsIdx, v) | rhsIdx <- [1..length (rhs r)], v <- vs ]-}

-- | returns the domain; which is fixed for a problem
domain :: Its -> Vars
domain = concatMap P.variables . args . _startterm


closed :: Its -> Bool
closed = TB.isDefined . _timebounds

ppRules :: Rules -> TB.Timebounds -> PP.Doc
ppRules rs tb =
  PP.table [(PP.AlignLeft, lhss), (PP.AlignLeft, rhss), (PP.AlignLeft, css), (PP.AlignLeft, tbs)]
  where
    lhss = map (PP.pretty . lhs) rsl
    rhss = map ((\p -> ppSpace PP.<> ppSep PP.<> ppSpace PP.<> p) . PP.pretty . rhs ) rsl
    css  = map (PP.pretty . con ) rsl
    tbs  = map ((ppSpace PP.<>) . PP.pretty . (tb M.!)) is
    ppSpace = PP.string "  "
    (is, rsl) = unzip rs

updateTimebounds :: Its -> TB.Timebounds -> Its
updateTimebounds prob tb = prob { _timebounds = TB.updates tb (_timebounds prob) }

instance PP.Pretty Its where
  pretty prob =
    pp "Rules:" (ppRules (_irules prob) (_timebounds prob))
    PP.<$$> pp "Signature:" (PP.pretty $ _signature prob)
    PP.<$$> pp "Flow Graph:" (PP.pretty (_tgraph prob))
    PP.<$$> pp "Sizebounds:" (PP.pretty (_sizebounds prob))
    where pp st p = PP.text st PP.<$$> PP.indent 2 p


-- mode
itsMode :: TctMode Its ()
itsMode = TctMode
  { modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = unit
  , modeModifyer        = const
  , modeAnswer          = answering }

answering :: Return (ProofTree Its) -> SomeAnswer
answering (Abort _)     = answer unknown
answering (Continue pt) = answer $ case F.toList pt of
  [prob] -> TB.totalBound (_timebounds prob)
  _      -> unknown



--- parse

parser :: String -> Either TctError Its
parser s = case PR.parse pProblem "" s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right (initialise p)

pProblem :: Parser ([Fun], [Var], [Rule])
pProblem = do
  void $ PR.parens (PR.symbol "GOAL COMPLEXITY")
  fs <- PR.parens (PR.symbol "STARTTERM" >> PR.parens (PR.symbol "FUNCTIONSYMBOLS" >> PR.many1 PR.identifier))
  vs <- PR.parens (PR.symbol "VAR" >> PR.many PR.identifier)
  rs <- PR.parens (PR.symbol "RULES" >> PR.many pRule)
  return (fs, vs, rs)
  PR.<?> "problem"

