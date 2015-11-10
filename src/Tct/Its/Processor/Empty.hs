module Tct.Its.Processor.Empty where


import qualified Tct.Core.Common.Pretty  as PP
import qualified Tct.Core.Common.Xml     as Xml
import qualified Tct.Core.Data           as T

import           Tct.Its.Data.Complexity (toComplexity)
import           Tct.Its.Data.Problem
import           Tct.Its.Data.Timebounds (totalBound)


empty :: ItsStrategy
empty = T.Apply EmptyProc

emptyDeclaration :: T.Declaration ('[] T.:-> ItsStrategy)
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
  toXml Empty    = Xml.elt "empty" []
  toXml NonEmpty = Xml.elt "nonempty" []

instance T.Processor EmptyProcessor where
  type ProofObject EmptyProcessor = EmptyProof
  type In  EmptyProcessor         = Its
  type Out EmptyProcessor         = Its
  type Forking EmptyProcessor     = T.Judgement

  execute EmptyProc prob =
    if isClosed prob
      then T.succeedWith0 Empty (const . T.timeUBCert . toComplexity $ totalBound (timebounds_ prob))
      else T.abortWith NonEmpty

