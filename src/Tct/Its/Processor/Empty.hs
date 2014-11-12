module Tct.Its.Processor.Empty where


import Tct.Core.Data
import qualified Tct.Core.Common.Pretty as PP

import Tct.Its.Data.Problem


empty :: Strategy Its
empty = Proc EmptyProc

emptyDeclaration :: Declaration ('[] :-> Strategy Its)
emptyDeclaration = declare "empty" ["Succeeds if the cost is defined, otherwise fails."] () empty


data EmptyProcessor = EmptyProc deriving Show

data EmptyProof
  = Empty
  | NonEmpty
  deriving Show

instance PP.Pretty EmptyProof where
  pretty Empty    = PP.text "Empty"
  pretty NonEmpty = PP.text "NonEmpty"

-- FIXME: wenn judgment is used; then we can not read the bound from answering
-- use dedicate either type or ??
instance Processor EmptyProcessor where
  type ProofObject EmptyProcessor = EmptyProof
  type Problem EmptyProcessor     = Its
  solve p prob 
    | closed prob = k $ Success (Id prob) Empty (const unbounded) -- TODO: compute asymptotic bound
    | otherwise   = k $ Fail NonEmpty
    where k = return . resultToTree p prob

