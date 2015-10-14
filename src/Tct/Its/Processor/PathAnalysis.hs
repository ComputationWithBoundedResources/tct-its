module Tct.Its.Processor.PathAnalysis where

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Xml          as Xml
import qualified Tct.Core.Data                as T

import           Tct.Common.ProofCombinators

import           Tct.Its.Data
import           Tct.Its.Data.Types
import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.TransitionGraph as TG


-- TODO: MS:
-- add a choice to label function symbols with the scc id
-- the idea is to identify different locations (possibly having the same function symbols)
data PathAnalysis = PathAnalysis
  deriving Show

data PathAnalysisProof
  = PathAnalysisProof { paths_ :: [[SCC RuleId]] }
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
  type In   PathAnalysis        = Its
  type Out PathAnalysis         = Its
  type Forking PathAnalysis     = []

  -- solve p prob | isClosed prob = return $ closedProof p prob
  execute PathAnalysis prob = case solvePathAnalysis prob of
    Nothing                -> T.abortWith (Applicable NoPathAnalysisProof)
    Just (pproof, newprob) -> T.succeedWith (Applicable pproof) bigAdd newprob 

solvePathAnalysis :: Its -> Maybe (PathAnalysisProof, [Its])
solvePathAnalysis prob
  | null (drop 1 paths) = Nothing
  | otherwise           = Just (pproof, newprob)
  where
    paths   = TG.rootsPaths (_tgraph prob)
    pproof  = PathAnalysisProof { paths_ = paths }
    newprob = map ((`restrictRules` prob) . concatMap theSCC) paths

pathAnalysis :: ItsStrategy
pathAnalysis = T.Apply PathAnalysis

pathAnalysisDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
pathAnalysisDeclaration = T.declare "pathAnalysis" [desc]  () pathAnalysis
  where desc = "We consider maximal paths from the root node in the transition graph, seperately."

