module Tct.Its.Data.Problem where


import           Control.Monad              (void)

import           Tct.Core.Common.Error      (TctError (..))
import qualified Tct.Core.Common.Parser     as PR
import qualified Tct.Core.Common.Pretty     as PP
import           Tct.Core.Main              (TctMode (..), unit)
import           Tct.Core.Processor.Trivial (failing)

import           Tct.Its.Data.Graph         (Graph, estimateGraph)
import           Tct.Its.Data.Rule


type Timebounds = [(Rule,Int)]
type Sizebounds = [(Rule,Int,Int)]

data Its = Its
  { rules      :: [Rule]
  , graph      :: Graph
  , timebounds :: Timebounds
  , sizebounds :: Sizebounds
  } deriving Show

instance PP.Pretty Its where
  pretty _ = undefined

itsMode :: TctMode Its ()
itsMode = TctMode
  { modeParser          = parser
  , modeStrategies      = []

  , modeDefaultStrategy = failing
  , modeOptions         = unit
  , modeModifyer        = const
  , modeAnswer          = undefined }

initialise :: [Rule] -> Its
initialise rs = Its
  { rules      = rs
  , graph      = estimateGraph rs
  , timebounds = []
  , sizebounds = [] }

parser :: String -> Either TctError Its
parser s = case PR.parse pProblem "" s of
  Left e  -> Left $ TctParseError (show e)
  Right p -> Right (initialise p)

pProblem :: Parser [Rule]
pProblem = do
  void $ PR.parens (PR.symbol "GOAL COMPLEXITY")
  void $ PR.parens (PR.symbol "STARTTERM" >> PR.parens (PR.symbol "FUNCTIONSYMBOLS" >> PR.many1 PR.identifier))
  void $ PR.parens (PR.symbol "VAR" >> PR.many PR.identifier)
  PR.parens (PR.symbol "RULES" >> PR.many pRule)
  PR.<?> "problem"

