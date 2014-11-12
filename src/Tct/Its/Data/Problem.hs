module Tct.Its.Data.Problem where


import qualified Data.Map                   as M
import           Control.Monad              (void)
import qualified Data.Foldable as F (toList)

import           Tct.Core.Data
import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Parser     as PR
import qualified Tct.Core.Common.Pretty     as PP
import           Tct.Core.Main              (TctMode (..), unit)
import           Tct.Core.Processor.Trivial (failing)

import qualified Tct.Common.Polynomial      as P

import           Tct.Its.Data.Graph         (Graph, estimateGraph)
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Sizebounds    as SB
import qualified Tct.Its.Data.Timebounds    as TB
import           Tct.Its.Data.Cost


type Signature = M.Map Fun Int

data Its = Its
  { rules      :: [Rule] -- split into strict/weak rules?
  , graph      :: Graph
  , signature  :: Signature
  , startterm  :: Term

  -- complexity o
  , timebounds :: TB.Timebounds
  , sizebounds :: SB.Sizebounds
  } deriving Show

closed :: Its -> Bool
closed = TB.isDefined . timebounds

ppRules :: [Rule] -> TB.Timebounds -> PP.Doc
ppRules rs tb = 
  PP.table [(PP.AlignLeft, lhss), (PP.AlignLeft, rhss), (PP.AlignLeft, css), (PP.AlignLeft, tbs)]
  where
    lhss = map (PP.pretty . lhs) rs
    rhss = map ((\p -> ppSpace PP.<> ppSep PP.<> ppSpace PP.<> p) . ppTerms . rhs ) rs
    css  = map (ppAtoms . con ) rs
    tbs  = map ((ppSpace PP.<>) . PP.pretty . (tb M.!)) rs
    ppSpace = PP.string "  "

updateTimebounds :: Its -> TB.Timebounds -> Its
updateTimebounds prob tb = prob { timebounds = TB.union (timebounds prob) tb }

instance PP.Pretty Its where
  pretty prob = 
    ppRules (rules prob) (timebounds prob)
    PP.<$$> PP.text (show $ signature prob)

itsMode :: TctMode Its ()
itsMode = TctMode
  { modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = unit
  , modeModifyer        = const
  , modeAnswer          = answering }

answering :: Return (ProofTree Its) -> SomeAnswer
answering (Abort _)     = answer omega
answering (Continue pt) = answer $ case F.toList pt of
  [prob] -> TB.cost (timebounds prob)
  _      -> omega

initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],vs, rs) = Its
  { rules      = rs
  , signature  = mkSignature rs

  , startterm  = Term fs (map P.variable vs)
  , graph      = estimateGraph rs

  , timebounds = TB.initialise rs
  , sizebounds = SB.initialise rs }
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"

mkSignature :: [Rule] -> Signature
mkSignature rs =  foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rs ]
  where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty

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

