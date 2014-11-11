-- cost expressions
module Tct.Its.Data.Cost
  (
  Cost

  , omega
  , poly

  , minimal
  , maximal
  ) where


import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Pretty    as PP

import qualified Tct.Common.Polynomial    as P

import           Tct.Its.Data.Rule        (Poly)


-- abstract cost type
data Cost
  = Omega
  | Poly Poly
  deriving (Eq, Show)

ppCost :: Cost -> PP.Doc
ppCost Omega    = PP.char '?'
ppCost (Poly p) = PP.pretty p

instance PP.Pretty Cost where
  pretty = ppCost


rank :: Cost -> Int
rank Omega    = 42
rank (Poly _) = 21

omega :: Cost
omega = Omega

poly :: Poly -> Cost
poly = Poly . P.mapCoefficients abs


-- minimum if computable
minimal :: Cost -> Cost -> Cost
minimal c1 c2 = if rank c2 < rank c1 then c2 else c1

maximal :: Cost -> Cost -> Cost
maximal c1 c2 = if rank c2 > rank c1 then c2 else c1

cadd :: Cost -> Cost -> Cost
cadd Omega _             = Omega
cadd _ Omega             = Omega
cadd (Poly p1) (Poly p2) = Poly (p1 `add` p2)

instance Additive Cost where
  zero = Poly (P.constant 0)
  add  = cadd

