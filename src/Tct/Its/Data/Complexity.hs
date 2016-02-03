module Tct.Its.Data.Complexity
  (
  Complexity (..)

  , unknown
  , poly
  , toComplexity

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
import qualified Tct.Core.Data             as T

import qualified Tct.Common.Polynomial    as P
import           Tct.Common.Ring

import Tct.Its.Data.Types (IPoly, Var)

data Complexity
  = Unknown
  | NPoly IPoly
  deriving (Eq, Show)

data Growth 
  = Max Int      -- ^ > x' = x; x' = y; x' = 3
  | MaxPlus Int  -- ^ > x' = x + 1; x' = y + 3
  | SumPlus Int  -- ^ > x' = y + z; but not x' = x + z
  | Unbounded deriving (Eq,Ord,Show)

ppComplexity :: Complexity -> PP.Doc
ppComplexity Unknown   = PP.char '?'
ppComplexity (NPoly p) = PP.pretty p

instance PP.Pretty Complexity where
  pretty = ppComplexity


unknown :: Complexity
unknown = Unknown

poly :: IPoly -> Complexity
poly = NPoly . P.mapCoefficients abs

compareComplexity :: Complexity -> Complexity -> Maybe Ordering
compareComplexity Unknown Unknown   = Just EQ
compareComplexity Unknown (NPoly _) = Just GT
compareComplexity (NPoly _) Unknown = Just LT
compareComplexity (NPoly p1) (NPoly p2)
  | all (==0) cs = Just EQ
  | all (>=0) cs = Just GT
  | all (<=0) cs = Just LT
  | otherwise    = Nothing
  where cs = P.coefficients (p1 `sub` p2)

toComplexity :: Complexity -> T.Complexity
toComplexity Unknown = T.Unknown
toComplexity (NPoly p)
  | deg < 0   = T.Poly Nothing
  | otherwise = T.Poly (Just deg)
  where deg = P.degree p

-- TODO: better bounds
-- minimum if computable
-- | left biased minimum
minimal :: Complexity -> Complexity -> Complexity
minimal Unknown c2 = c2
minimal c1 _       = c1

maximal :: Complexity -> Complexity -> Complexity
maximal c1 c2 = case compareComplexity c1 c2 of
  Just EQ -> c1
  Just GT -> c1
  Just LT -> c2
  Nothing -> case (c1,c2) of
    (NPoly p1, NPoly p2) -> NPoly $ P.zipCoefficientsWith max p1 p2
    _                    -> c1 `cadd` c2

cadd :: Complexity -> Complexity -> Complexity
cadd Unknown _             = Unknown
cadd _ Unknown             = Unknown
cadd (NPoly p1) (NPoly p2) = NPoly (p1 `add` p2)

cmul :: Complexity -> Complexity -> Complexity
cmul Unknown _             = Unknown
cmul _ Unknown             = Unknown
cmul (NPoly p1) (NPoly p2) = NPoly (p1 `mul` p2)

instance Additive Complexity where
  zero = NPoly (P.constant 0)
  add  = cadd

instance Multiplicative Complexity where
  one = NPoly (P.constant 1)
  mul = cmul

activeVariables :: Complexity -> [Var]
activeVariables Unknown   = []
activeVariables (NPoly p) = P.variables p

compose :: Complexity -> M.Map Var Complexity -> Complexity
compose Unknown _ = Unknown
compose c@(NPoly p) m 
  | all (`elem` defined) (activeVariables c) = poly $ P.substituteVariables p (M.fromAscList polys)
  | otherwise                                = Unknown
  where
    polys   = [ (v,np) | (v, NPoly np) <- M.toAscList m ]
    defined = fst (unzip polys)


growth :: Complexity -> Growth
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

instance PP.Pretty Growth where
  pretty (Max i)     = PP.text ".=" PP.<+> PP.int i
  pretty (MaxPlus i) = PP.text ".+" PP.<+> PP.int i
  pretty (SumPlus i) = PP.text ".*" PP.<+> PP.int i
  pretty Unbounded   = PP.text ".?"

isSumPlus :: Growth -> Bool
isSumPlus (SumPlus _) = True
isSumPlus _           = False
