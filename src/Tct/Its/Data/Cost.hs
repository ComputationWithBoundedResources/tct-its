module Tct.Its.Data.Cost
  (
  Cost (..)

  , omega
  , poly

  , minimal
  , maximal

  , activeVariables
  ) where


import           Tct.Core.Common.SemiRing
import qualified Tct.Core.Common.Pretty    as PP

import qualified Tct.Common.Polynomial    as P

import           Tct.Its.Data.Types


ppCost :: Cost -> PP.Doc
ppCost Omega    = PP.char '?'
ppCost (NPoly p) = PP.pretty p

instance PP.Pretty Cost where
  pretty = ppCost


rank :: Cost -> Int
rank Omega    = 42
rank (NPoly _) = 21

omega :: Cost
omega = Omega

poly :: IPoly -> Cost
poly = NPoly . P.mapCoefficients abs


-- minimum if computable
minimal :: Cost -> Cost -> Cost
minimal c1 c2 = if rank c2 < rank c1 then c2 else c1

maximal :: Cost -> Cost -> Cost
maximal c1 c2 = if rank c2 > rank c1 then c2 else c1

cadd :: Cost -> Cost -> Cost
cadd Omega _             = Omega
cadd _ Omega             = Omega
cadd (NPoly p1) (NPoly p2) = NPoly (p1 `add` p2)

instance Additive Cost where
  zero = NPoly (P.constant 0)
  add  = cadd

activeVariables :: Cost -> [Var]
activeVariables Omega     = []
activeVariables (NPoly p) = P.variables p


