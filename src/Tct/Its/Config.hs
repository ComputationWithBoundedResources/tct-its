module Tct.Its.Config
  ( fromFile
  , fromString

  , ItsConfig
  , itsConfig
  , its
  , itsDeclarations
  ) where


import           Control.Monad          (void)

import           Tct.Core
import qualified Tct.Core.Common.Parser as PR

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import           Tct.Its.Processor
import           Tct.Its.Strategy


type ItsConfig = TctConfig Its

itsConfig :: ItsConfig
itsConfig = defaultTctConfig fromFile
  `withDefaultStrategy` runtime

its :: Declared Its Its => ItsConfig -> IO ()
its = tct3

itsDeclarations :: [StrategyDeclaration Its Its]
itsDeclarations = SD runtimeDeclaration: defaultDecls

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

