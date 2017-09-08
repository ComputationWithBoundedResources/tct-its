module Tct.Its.Config
  ( fromFile
  , fromString

  , runIts
  , ItsConfig
  , itsConfig

  , putAnswerMultivariate
  ) where


import           Control.Monad           (void)
import           Data.Foldable           (toList)
import           Data.Typeable           (cast)

import           Tct.Core
import qualified Tct.Core.Common.Parser  as PR
import qualified Tct.Core.Common.Pretty  as PP
import qualified Tct.Core.Data           as T

import           Tct.Its.Data.Problem
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Timebounds (totalBound)
import           Tct.Its.Strategies      (runtime)


type ItsConfig = TctConfig Its

itsConfig :: ItsConfig
itsConfig = defaultTctConfig fromFile
  `withDefaultStrategy` runtime

runIts :: Declared Its Its => ItsConfig -> IO ()
runIts = runTct

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

-- XXX: MS: a hack to print multivariate bounds
-- only works when there are no splits in the proof
putAnswerMultivariate :: T.ProofTree t -> PP.Doc
putAnswerMultivariate (T.Open _)           = ppM
putAnswerMultivariate (T.Success pn _ pts) = case toList pts of
  []   -> case (cast (T.problem pn) :: Maybe Its) of
    Just p  -> PP.pretty $ totalBound $ timebounds_ p
    Nothing -> ppM
  [pt] -> putAnswerMultivariate pt
  _    -> PP.text "Tct.Its.Config: CHECK ME"
putAnswerMultivariate (T.Failure _) = ppM

ppM :: PP.Doc
ppM = PP.text "MAYBE"

