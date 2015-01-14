module Tct.Its.Processor.Empty where


import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Xml    as Xml
import qualified Tct.Core.Data          as T

import Tct.Its.Data.Complexity (toComplexity)
import Tct.Its.Data.Problem 
import Tct.Its.Data.Timebounds (totalBound)


empty :: T.Strategy Its
empty = T.Proc EmptyProc

emptyDeclaration :: T.Declaration ('[] T.:-> T.Strategy Its)
emptyDeclaration = T.declare "empty" ["Succeeds if the cost is defined, otherwise fails."] () empty


data EmptyProcessor = EmptyProc deriving Show

data EmptyProof
  = Empty
  | NonEmpty
  deriving Show

instance PP.Pretty EmptyProof where
  pretty Empty    = PP.text "Empty"
  pretty NonEmpty = PP.text "NonEmpty"

instance Xml.Xml EmptyProof where
  toXml Empty    = Xml.text "empty"
  toXml NonEmpty = Xml.text "nonempty"

instance T.Processor EmptyProcessor where
  type ProofObject EmptyProcessor = EmptyProof
  type Problem EmptyProcessor     = Its
  type Forking EmptyProcessor     = T.Judgement
  solve p prob = return . T.resultToTree p prob $ 
    if isClosed prob
      then T.Success T.Judgement Empty (const . T.timeUBCert . toComplexity $ totalBound (_timebounds prob))
      else T.Fail NonEmpty

