module Tct.Its.Processor.Empty where


import Tct.Core.Data
import qualified Tct.Core.Common.Pretty as PP

import Tct.Its.Data.Problem


emptyProcessor :: EmptyProcessor
emptyProcessor = EmptyProc

emptyD :: Declaration ('[] :-> Strategy Its)
emptyD = declaration emptyProcessor

empty :: Strategy Its
empty = Proc EmptyProc

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
    | closed prob = go $ Success (Id prob) Empty (const unbounded) -- TODO: compute asymptotic bound
    | otherwise   = go $ Fail NonEmpty
    where go = return . resultToTree p prob
  declaration _ = declareProcessor "empty" [] () (Proc EmptyProc)

