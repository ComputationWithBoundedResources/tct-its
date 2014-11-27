module Tct.Its.Data.Cost
  (
  Cost (..)

  , unknown
  , poly

  , minimal
  , maximal
  , compose

  , Growth (..)
  , growth
  , isSumPlus
  , activeVariables
  ) where


import qualified Data.Map.Strict as M

import qualified Tct.Core.Common.Pretty    as PP

import qualified Tct.Common.Polynomial    as P
import           Tct.Common.Ring

import Tct.Its.Data.Types (IPoly, Var)

data Cost
  = Unknown
  | NPoly IPoly
  deriving (Eq, Show)

data Growth 
  = Max Int      -- ^ > x' = x; x' = y; x' = 3
  | MaxPlus Int  -- ^ > x' = x + 1; x' = y + 3
  | SumPlus Int  -- ^ > x' = y + z; but not x' = x + z
  | Unbounded deriving (Eq,Ord,Show)

ppCost :: Cost -> PP.Doc
ppCost Unknown   = PP.char '?'
ppCost (NPoly p) = PP.pretty p

instance PP.Pretty Cost where
  pretty = ppCost


unknown :: Cost
unknown = Unknown

poly :: IPoly -> Cost
poly = NPoly . P.mapCoefficients abs

compareCost :: Cost -> Cost -> Maybe Ordering
compareCost Unknown Unknown   = Just EQ
compareCost Unknown (NPoly _) = Just GT
compareCost (NPoly _) Unknown = Just LT
compareCost (NPoly p1) (NPoly p2)
  | all (==0) cs = Just EQ
  | all (>=0) cs = Just GT
  | all (<=0) cs = Just LT
  | otherwise    = Nothing
  where cs = P.coefficients (p1 `sub` p2)


-- TODO: better bounds
-- minimum if computable
minimal :: Cost -> Cost -> Cost
minimal c1 _ = c1

maximal :: Cost -> Cost -> Cost
maximal c1 c2 = case compareCost c1 c2 of
  Just EQ -> c1
  Just GT -> c1
  Just LT -> c2
  _ -> c1 `cadd` c2 -- FIXME: very rough bound

cadd :: Cost -> Cost -> Cost
cadd Unknown _             = Unknown
cadd _ Unknown             = Unknown
cadd (NPoly p1) (NPoly p2) = NPoly (p1 `add` p2)

cmul :: Cost -> Cost -> Cost
cmul Unknown _             = Unknown
cmul _ Unknown             = Unknown
cmul (NPoly p1) (NPoly p2) = NPoly (p1 `mul` p2)

instance Additive Cost where
  zero = NPoly (P.constant 0)
  add  = cadd

instance Multiplicative Cost where
  one = NPoly (P.constant 1)
  mul = cmul

activeVariables :: Cost -> [Var]
activeVariables Unknown     = []
activeVariables (NPoly p) = P.variables p

compose :: Cost -> M.Map Var Cost -> Cost
compose Unknown _ = Unknown
compose c@(NPoly p) m 
  | all (`elem` defined) (activeVariables c) = poly $ P.substituteVariables p (M.fromAscList polys)
  | otherwise                                = Unknown
  where
    polys   = [ (v,np) | (v, NPoly np) <- M.toAscList m ]
    defined = fst (unzip polys)


growth :: Cost -> Growth
growth Unknown = Unbounded
growth (NPoly p)
  | not (P.isStronglyLinear p) = Unbounded
  | ncoeffs == 0               = Max c
  | ncoeffs == 1 && c == 0     = Max 0
  | ncoeffs == 1               = MaxPlus c
  | otherwise                  = SumPlus c
  where 
    (cs,c)  = P.coefficients' p
    ncoeffs = length cs


isSumPlus :: Growth -> Bool
isSumPlus (SumPlus _) = True
isSumPlus _           = False
