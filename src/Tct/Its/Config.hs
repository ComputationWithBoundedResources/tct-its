module Tct.Its.Config
  ( fromFile
  , fromString

  , ItsConfig
  , itsConfig
  , its
  ) where


import           Control.Monad          (void)

import           Tct.Core               (addStrategies)
import qualified Tct.Core.Common.Parser as PR
import qualified Tct.Core.Data          as T
import qualified Tct.Core.Main          as T

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import           Tct.Its.Strategy


type ItsConfig = T.TctConfig Its

itsConfig :: ItsConfig
itsConfig = T.defaultTctConfig fromFile
  `withDefaultStrategy` runtime
  `addStrategies`
    [ T.SD runtimeDeclaration ]

its :: ItsConfig -> IO ()
its = T.tct3

--- parse

fromFile :: FilePath -> IO (Either String Its)
fromFile = fmap fromString . readFile

fromString :: String -> Either String Its
fromString s = case PR.parse pProblem "" s of
  Left e  -> Left  (show e)
  Right p -> Right (initialise p)

pProblem :: Parser ([Fun], [Var], [Rule])
pProblem = do
  void $ PR.parens (PR.symbol "GOAL COMPLEXITY")
  fs <- PR.parens (PR.symbol "STARTTERM" >> PR.parens (PR.symbol "FUNCTIONSYMBOLS" >> PR.many1 PR.identifier))
  vs <- PR.parens (PR.symbol "VAR" >> PR.many PR.identifier)
  rs <- PR.parens (PR.symbol "RULES" >> PR.many pRule)
  return (fs, vs, rs)
  PR.<?> "problem"

