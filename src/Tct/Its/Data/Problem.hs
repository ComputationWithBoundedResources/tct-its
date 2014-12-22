module Tct.Its.Data.Problem
  ( Its (..)

  , validate

  --, rvss
  , domain
  , closed
  , updateTimebounds

  , itsMode
  ) where


import           Control.Monad                    (void)
import qualified Data.Foldable                    as F (toList)
import qualified Data.List                        as L (find)
import qualified Data.Map                         as M
import           Data.Maybe                       (fromMaybe)

import           Tct.Core.Common.Error            (TctError (..))
import qualified Tct.Core.Common.Parser           as PR
import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Data as T
import           Tct.Core.Main                    (TctMode (..), unit)
import           Tct.Core.Processor.Trivial       (failing)

import qualified Tct.Common.Answer           as A
import qualified Tct.Common.Polynomial            as P

import           Tct.Its.Data.Cost
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
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
initialise ([fs],_, rsl) = Its
  { _irules          = irules
  , _signature       = mkSignature

  , _startterm       = Term fs (args $ lhs start)
  , _tgraph          = tgraph
  , _rvgraph         = Nothing

  , _timebounds      = TB.initialise ris (initialRules tgraph)
  , _sizebounds      = Nothing
  , _localSizebounds = Nothing }
  where
    start = error "startterm not defined" `fromMaybe` L.find (\r -> fun (lhs r) == fs) rsl
    tgraph = estimateGraph irules
    irules = zip [0..] rsl
    ris = fst (unzip irules)
    mkSignature = foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rsl ]
      where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"


validate :: Rules -> Bool
validate = all validRule
  where
    validRule (_,ru) = case rhs ru of
      [r] -> all P.isLinear (args r)
      _   -> False

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
  PP.table
    [ (PP.AlignLeft, map (\i -> PP.int i PP.<> PP.dot PP.<> PP.space) is)
    , (PP.AlignLeft, lhss)
    , (PP.AlignLeft, rhss)
    , (PP.AlignLeft, css)
    , (PP.AlignLeft, tbs)]
  where
    lhss = map (PP.pretty . lhs) rsl
    rhss = map ((\p -> ppSpace PP.<> ppSep PP.<> ppSpace PP.<> p) . PP.pretty . rhs ) rsl
    css  = map (PP.pretty . con ) rsl
    tbs  = map ((ppSpace PP.<>) . PP.pretty . (tb `TB.boundOf`)) is
    ppSpace = PP.string "  "
    (is, rsl) = unzip rs

updateTimebounds :: Its -> TB.Timebounds -> Its
updateTimebounds prob tb = prob { _timebounds = TB.updates tb (_timebounds prob) }

instance PP.Pretty Its where
  pretty prob =
    pp "Rules:" (ppRules (_irules prob) (_timebounds prob))
    PP.<$$> pp "Signature:" (PP.pretty $ _signature prob)
    PP.<$$> pp "Flow Graph:" (PP.pretty (_tgraph prob))
    --PP.<$$> pp "Sizebounds:" (PP.pretty (_sizebounds prob))
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

answering :: T.Return (T.ProofTree Its) -> T.SomeAnswer
answering (T.Abort _)     = T.answer A.Unknown
answering (T.Continue pt) = T.answer . toAnswer . toComplexity $ case F.toList pt of
  [prob] -> TB.totalBound (_timebounds prob)
  _      -> unknown
  where
    toAnswer T.Unknown = A.Unknown
    toAnswer c         = A.Yes(T.Unknown, c)

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

