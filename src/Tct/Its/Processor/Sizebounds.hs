module Tct.Its.Processor.Sizebounds
  (
  sizebounds
  , sizeboundsDeclaration
  ) where


import           Control.Monad.Trans              (liftIO)
--import qualified Data.Graph.Inductive.Dot         as Gr
import           Data.Maybe                       (fromMaybe)

import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Common.Xml              as Xml
import           Tct.Core (withProblem, (>>>))
import qualified Tct.Core.Data as T

import           Tct.Common.ProofCombinators

import           Tct.Its.Data.Problem
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import qualified Tct.Its.Data.LocalSizebounds     as LB (compute)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import qualified Tct.Its.Data.ResultVariableGraph as RVG (compute)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
import qualified Tct.Its.Data.Sizebounds          as SB (initialise, updateSizebounds)



-- | Computes local sizebounds; Initialises global sizebounds.
localSizebound :: T.Strategy Its
localSizebound = T.Proc LocalSizeboundsProc

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

instance Xml.Xml LocalSizeboundsProof where
  toXml _ = Xml.text "localsizebounds"

instance T.Processor LocalSizeboundsProcessor where
  type ProofObject LocalSizeboundsProcessor = ApplicationProof LocalSizeboundsProof
  type Problem LocalSizeboundsProcessor     = Its
  type Forking LocalSizeboundsProcessor     = T.Optional T.Id

  solve p prob | isClosed prob = return $ closedProof p prob
  solve p prob = do
    nprob <- liftIO $ initialiseSizebounds prob
    let pproof = LocalSizeboundsProof (domain prob, error "proc sizeb" `fromMaybe` _localSizebounds nprob) (error "proc rv" `fromMaybe` _rvgraph nprob)
    return $ progress p prob (Progress nprob) (Applicable pproof)



data SizeboundsProcessor = SizeboundsProc deriving Show

data SizeboundsProof = SizeboundsProof (Vars, Sizebounds) deriving Show

instance PP.Pretty SizeboundsProof where
  pretty (SizeboundsProof vsbounds) = 
    PP.text "Sizebounds computed:"
    PP.<$$> PP.indent 2 (PP.pretty vsbounds)

instance Xml.Xml SizeboundsProof where
  toXml _ = Xml.text "sizebounds"

instance T.Processor SizeboundsProcessor where
  type ProofObject SizeboundsProcessor = ApplicationProof SizeboundsProof
  type Problem SizeboundsProcessor     = Its
  type Forking SizeboundsProcessor     = T.Optional T.Id


  solve p prob | isClosed prob = return $ closedProof p prob
  solve p prob = return $
    if _sizebounds prob /= _sizebounds nprob 
      then progress p prob (Progress nprob) (Applicable pproof)
      else progress p prob NoProgress (Applicable pproof)
    where 
      nprob = updateSizebounds prob
      pproof = SizeboundsProof (domain prob, error "sizebound" `fromMaybe` _sizebounds nprob)

updateSizebounds :: Its -> Its
updateSizebounds prob = prob {_sizebounds = Just sbounds'} where
  sbounds' = SB.updateSizebounds 
    (_tgraph prob) 
    (error "update rvgraph" `fromMaybe` _rvgraph prob) 
    (_timebounds prob) 
    (error "update sizebounds" `fromMaybe` _sizebounds prob)  
    (error "update localsizebounds" `fromMaybe` _localSizebounds prob)

-- | Updates sizebounds.
sizebounds :: T.Strategy Its
sizebounds = withProblem $ 
  \prob -> if sizeIsDefined prob then sb else localSizebound >>> sb
  where sb = T.Proc SizeboundsProc

sizeboundsDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
sizeboundsDeclaration = T.declare "sizebounds" [desc] () sizebounds
  where desc = "Computes global sizebounds using timebounds."

