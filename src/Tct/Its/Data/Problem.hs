module Tct.Its.Data.Problem
  ( Its (..)

  , validate

  --, rvss
  , domain
  , sizeIsDefined
  , isClosed
  , closedProof
  , updateTimebounds

  , Progress (..)
  , hasProgress
  , progress

  , itsMode
  ) where


import           Control.Monad                    (void)
import qualified Data.IntMap.Strict               as IM
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (isJust)

import           Tct.Core.Common.Error            (TctError (..))
import qualified Tct.Core.Common.Parser           as PR
import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Data                    as T
import           Tct.Core.Main                    (TctMode (..), unit)
import           Tct.Core.Processor.Trivial       (failing)

import           Tct.Common.ProofCombinators
import qualified Tct.Common.Answer                as A
import qualified Tct.Common.Polynomial            as P

import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
import           Tct.Its.Data.Timebounds          (Timebounds)
import qualified Tct.Its.Data.Timebounds          as TB
import           Tct.Its.Data.TransitionGraph     (TGraph, estimateGraph)
import           Tct.Its.Data.Types
import           Tct.Its.Data.Complexity (toComplexity)


data Its = Its
  { _irules          :: Rules
  , _signature       :: Signature
  , _startterm       :: Term
  , _startrules      :: Rules

  , _tgraph          :: TGraph
  , _rvgraph         :: Maybe RVGraph

  , _timebounds      :: Timebounds
  , _sizebounds      :: Maybe Sizebounds
  , _localSizebounds :: Maybe LocalSizebounds
  } deriving Show

sizeIsDefined :: Its -> Bool
sizeIsDefined prob = isJust (_rvgraph prob) && isJust (_sizebounds prob) && isJust (_localSizebounds prob)

initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],_, rsl) = Its
  { _irules          = allRules
  , _signature       = mkSignature

  , _startterm       = Term fs (args $ lhs start)
  , _startrules      = startRules

  , _tgraph          = tgraph
  , _rvgraph         = Nothing

  , _timebounds      = TB.initialise (IM.keys allRules) (IM.keys startRules)
  , _sizebounds      = Nothing
  , _localSizebounds = Nothing }
  where
    allRules   = IM.fromList $ zip [0..] rsl
    startRules = IM.filter (\r -> fun (lhs r) == fs) allRules
    start      = snd $ IM.findMin startRules
    tgraph = estimateGraph allRules
    mkSignature = foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rsl ]
      where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"


validate :: [Rule] -> Bool
validate = all validRule
  where
    validRule ru = case rhs ru of
      [r] -> all P.isLinear (args r)
      _   -> False

{-rvss :: Vars -> Rules -> [RV]-}
{-rvss vs = concatMap k-}
  {-where k (i,r) = [ (i, rhsIdx, v) | rhsIdx <- [1..length (rhs r)], v <- vs ]-}

-- | returns the domain; which is fixed for a problem
domain :: Its -> Vars
domain = concatMap P.variables . args . _startterm


isClosed :: Its -> Bool
isClosed = TB.allDefined . _timebounds


data Progress a = Progress a | NoProgress

cert :: T.Optional T.Id T.Certificate -> T.Certificate
cert T.Null           = T.timeUBCert T.constant
cert (T.Opt (T.Id c)) = c


progress :: (T.Processor p, T.Forking p ~ T.Optional T.Id)
  => p -> T.Problem p -> Progress (T.Problem p) -> T.ProofObject p -> T.Return (T.ProofTree (T.Problem p))
progress p prob (Progress prob') proof = T.resultToTree p prob $ T.Success (T.Opt $ T.Id prob') proof cert
progress p prob NoProgress proof       = T.resultToTree p prob $ T.Fail proof

closedProof :: (T.Processor p , T.Forking p ~ T.Optional a, T.Problem p ~ Its, T.ProofObject p ~ ApplicationProof p1)
  => p -> Its -> T.Return (T.ProofTree Its)
closedProof p prob = T.resultToTree p prob $ T.Success T.Null Closed (const $ T.timeUBCert b)
    where b = toComplexity $ TB.totalBound (_timebounds prob)

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
    rhss = map ((\p -> PP.space PP.<> ppSep PP.<+> p PP.<> PP.space) . PP.pretty . rhs ) rsl
    css  = map (PP.pretty . con ) rsl
    tbs  = map ((PP.space PP.<>) . PP.pretty . (tb `TB.tboundOf`)) is
    (is, rsl) = unzip (IM.assocs rs)


hasProgress :: Its -> TB.TimeboundsMap -> Bool
hasProgress prob = TB.hasProgress (_timebounds prob)

updateTimebounds :: Its -> TB.TimeboundsMap -> Its
updateTimebounds prob tb = prob { _timebounds = TB.updates (_timebounds prob) tb }

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
  , modeAnswer          = A.answering }

--answering :: T.Return (T.ProofTree Its) -> T.SomeAnswer
--answering (T.Abort _)     = T.answer A.Unknown
--answering (T.Continue pt) = T.answer . toAnswer . toComplexity $ case F.toList pt of
  --[prob] -> TB.totalBound (_timebounds prob)
  --_      -> unknown
  --where
    --toAnswer T.Unknown = A.Unknown
    --toAnswer c         = A.Yes(T.Unknown, c)

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

