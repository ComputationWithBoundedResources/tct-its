module Tct.Its.Data.Problem 
  ( Its (..)
  --, rvss
  , domain
  , closed
  , updateTimebounds

  , itsMode
  ) where


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

import           Tct.Its.Data.TransitionGraph  (estimateGraph)
import           Tct.Its.Data.Rule
import qualified Tct.Its.Data.Timebounds    as TB
import           Tct.Its.Data.Cost
import           Tct.Its.Data.Types


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
updateTimebounds prob tb = prob { _timebounds = TB.union (_timebounds prob) tb }

instance PP.Pretty Its where
  pretty prob = 
    ppRules (_rules prob) (_timebounds prob)
    PP.<$$> PP.text (show $ _signature prob)


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

initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],vs, rsl) = Its
  { _rules      = rs
  , _signature  = mkSignature rsl

  , _startterm  = Term fs (map P.variable vs)
  , _tgraph     = estimateGraph rsl
  , _rvgraph    = Nothing 

  , _timebounds = TB.initialise rs
  , _sizebounds = Nothing
  , _localSizebounds = Nothing
  }
  where rs = zip [0..] rsl
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

