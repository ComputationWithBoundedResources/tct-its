module Tct.Its.Processor.Sizebounds
  (
  sizebounds
  , sizeboundsDeclaration
  ) where


import           Control.Monad.Trans              (liftIO)
--import qualified Data.Graph.Inductive.Dot         as Gr
import           Data.Maybe                       (fromJust, isJust)

import qualified Tct.Core.Common.Pretty           as PP
import           Tct.Core (withProblem, (>>>))
import           Tct.Core.Data

import           Tct.Its.Data.Problem
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds     as LB (compute)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import qualified Tct.Its.Data.ResultVariableGraph as RVG (compute)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
import qualified Tct.Its.Data.Sizebounds          as SB (initialise, updateSizebounds)



-- MS: local sizebounds need SMT calls; 
-- | Computes local sizebounds; Initialises global sizebounds.
localSizebound :: Strategy Its
localSizebound = Proc LocalSizeboundsProc



-- | Sets localSizebounds, rvgraph, sizebounds if not already defined.
initialiseSizebounds :: Its -> IO Its
initialiseSizebounds prob = case _localSizebounds prob of
  Just _ ->  return prob
  Nothing -> newprob
  where
    newprob = do
      lbounds <- LB.compute (domain prob) (_irules prob)
      let
        rvgraph = RVG.compute (_tgraph prob) lbounds
        sbounds = SB.initialise lbounds
      -- liftIO $ writeFile "/tmp/rvgraph.dot" $ maybe "Gr" (Gr.showDot . Gr.fglToDot) (_rvgraph prob)
      return $ prob {_localSizebounds = Just lbounds, _rvgraph = Just rvgraph, _sizebounds = Just sbounds}


data LocalSizeboundsProcessor = LocalSizeboundsProc deriving Show
data LocalSizeboundsProof     = LocalSizeboundsProof (Vars, LocalSizebounds) RVGraph deriving Show

instance PP.Pretty LocalSizeboundsProof where
  pretty (LocalSizeboundsProof vlbounds _) = 
    PP.text "LocalSizebounds generated; rvgraph"
    PP.<$$> PP.indent 2 (PP.pretty vlbounds)

instance Processor LocalSizeboundsProcessor where
  type ProofObject LocalSizeboundsProcessor = LocalSizeboundsProof
  type Problem LocalSizeboundsProcessor     = Its
  solve p prob = do
    nprob <- liftIO $ initialiseSizebounds prob
    let pproof = LocalSizeboundsProof (domain prob, fromJust $ _localSizebounds nprob) (fromJust $ _rvgraph nprob)
    return $ resultToTree p prob $ Success (Id nprob) pproof (\(Id c) -> c)





data SizeboundsProcessor = SizeboundsProc deriving Show

data SizeboundsProof = SizeboundsProof (Vars, Sizebounds) deriving Show

instance PP.Pretty SizeboundsProof where
  pretty (SizeboundsProof vsbounds) = 
    PP.text "Sizebounds computed:"
    PP.<$$> PP.indent 2 (PP.pretty vsbounds)

instance Processor SizeboundsProcessor where
  type ProofObject SizeboundsProcessor = SizeboundsProof
  type Problem SizeboundsProcessor     = Its
  solve p prob = return $ resultToTree p prob $
    if (_sizebounds prob) /= (_sizebounds nprob) 
      then Success (Id nprob) pproof (\(Id c) -> c)
      else Fail $ pproof
    where 
      nprob = updateSizebounds prob
      pproof = SizeboundsProof (domain prob, fromJust $ _sizebounds nprob)

updateSizebounds :: Its -> Its
updateSizebounds prob = prob {_sizebounds = Just sbounds'} where
  sbounds' = SB.updateSizebounds 
    (_tgraph prob) 
    (fromJust $ _rvgraph prob) 
    (_timebounds prob) 
    (fromJust $ _sizebounds prob)  
    (fromJust $ _localSizebounds prob)

-- | Updates sizebounds.
sizebounds :: Strategy Its
sizebounds = withProblem $ 
  \prob -> if isJust (_sizebounds prob) then sb else localSizebound >>> sb
  where sb = Proc SizeboundsProc

sizeboundsDeclaration :: Declaration ('[] :-> Strategy Its)
sizeboundsDeclaration = declare "sizebounds" [desc] () sizebounds
  where desc = "Computes global sizebounds using timebounds."

