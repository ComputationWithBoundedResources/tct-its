module Tct.Its.Processor.PathAnalysis where

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.TransitionGraph as TG


data PathAnalysis = PathAnalysis
  deriving Show

data PathAnalysisProof
  = PathAnalysisProof { paths_ :: [TG.TPath] }
  | NoPathAnalysisProof
  deriving Show

instance PP.Pretty PathAnalysisProof where
  pretty NoPathAnalysisProof   = PP.text "No paths."
  pretty p@PathAnalysisProof{} = PP.vcat
    [ PP.text "We analyse following paths seperately:"
    , PP.indent 2 $ PP.enumerate' (paths_ p) ]

instance Xml.Xml PathAnalysisProof where
  toXml NoPathAnalysisProof = Xml.elt "nopathanalysis" []
  toXml PathAnalysisProof{} = Xml.elt "pathanalysis" []

instance T.Processor PathAnalysis where
  type ProofObject PathAnalysis = ApplicationProof PathAnalysisProof
  type Problem PathAnalysis     = Its
  type Forking PathAnalysis     = []

  -- solve p prob | isClosed prob = return $ closedProof p prob
  solve p prob = return . T.resultToTree p prob $ case solvePathAnalysis prob of
    Nothing                -> T.Fail (Applicable NoPathAnalysisProof)
    Just (pproof, newprob) -> T.Success newprob (Applicable pproof) bigAdd

solvePathAnalysis :: Its -> Maybe (PathAnalysisProof, [Its])
solvePathAnalysis prob
  | null (drop 1 paths) = Nothing
  | otherwise           = Just (pproof, newprob)
  where
    paths   = TG.rootsMaxPaths (_tgraph prob)
    pproof  = PathAnalysisProof { paths_ = paths }
    newprob = map (`restrictRules` prob) paths

pathAnalysis :: T.Strategy Its
pathAnalysis = T.Proc PathAnalysis

pathAnalysisDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
pathAnalysisDeclaration = T.declare "pathAnalysis" [desc]  () pathAnalysis
  where desc = "We consider maximal paths from the root node in the transition graph, seperately."

