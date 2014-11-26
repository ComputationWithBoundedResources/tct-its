module Tct.Its.Processor.KnowledgePropagation
  (
  boundTrivialSCCs
  , boundTrivialSCCsDeclaration
  ) where

import qualified Data.Map.Strict              as M

import qualified Tct.Core.Common.Pretty       as PP
import           Tct.Core.Common.SemiRing
import           Tct.Core.Data

import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds      as TB
import qualified Tct.Its.Data.TransitionGraph as TG


boundTrivialSCCs :: Strategy Its
boundTrivialSCCs = Proc TrivialSCCs

boundTrivialSCCsDeclaration :: Declaration ('[] :-> Strategy Its)
boundTrivialSCCsDeclaration = declare "simp" [desc]  () boundTrivialSCCs
  where desc = "Trivial SCCs in the transition graph admit a timebound 1. This processor always Succeeds."


-- 

data PropagationProcessor
  = TrivialSCCs -- ^ Trivial SCCs in the transition graph are trivially bounded. Always Succeeds.
  deriving Show

data PropagationProof = PropagationProof
 { _proc  :: PropagationProcessor
 , _times :: TB.Timebounds
 } deriving Show

instance PP.Pretty PropagationProof where
  pretty pproof = case _proc pproof of 
    TrivialSCCs -> PP.text "All trivial SCCs of the transition graph admit timebound 1."

instance Processor PropagationProcessor where
  type ProofObject PropagationProcessor = PropagationProof
  type Problem PropagationProcessor     = Its

  solve p@(TrivialSCCs) prob = return $ resultToTree p prob $ Success (Id newprob) pproof (\(Id c) -> c)
    where (pproof, newprob) = solveTrivialSCCs prob

solveTrivialSCCs :: Its -> (PropagationProof, Its)
solveTrivialSCCs prob = (pproof, newprob)
  where
  sccs = TG.trivialSCCs (_tgraph prob)
  pproof = PropagationProof 
    { _proc  = TrivialSCCs 
    , _times = M.fromList [(scc,c) | scc <- sccs, let c = one ]}
  newprob = prob {_timebounds = TB.union new old } 
    where (old,new) = (_timebounds prob, _times pproof)


-- 

