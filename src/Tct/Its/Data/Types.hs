module Tct.Its.Data.Types where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L

import qualified Tct.Common.SMT as SMT
import qualified Tct.Common.Polynomial as P
import qualified Tct.Core.Common.Pretty as PP


type Signature = M.Map Fun Int

restrictSignature :: S.Set Fun -> Signature -> Signature
restrictSignature fs = M.filterWithKey (\k _ -> k `S.member` fs)

instance PP.Pretty Signature where
  pretty sig = PP.semiBraces $ map (\(f,i) -> PP.tupled [PP.pretty f, PP.pretty i]) (M.toList sig)

type AIPoly v = P.Polynomial Int v

data ATerm f v = Term 
  { fun  :: f  
  , args :: [AIPoly v]
  } deriving (Eq, Ord, Show)

data AAtom v
  = Eq (AIPoly v) (AIPoly v)
  | Gte (AIPoly v) (AIPoly v)
  deriving (Eq, Ord, Show)

data ARule f v = Rule
  { lhs :: ATerm f v
  , rhs :: [ATerm f v]
  , con :: [AAtom v] }
  deriving (Eq, Ord, Show)


type AConstraint v = [AAtom v]
type Vars  = [Var]
type RuleId = Int
type ComId = Int
type Rules = IM.IntMap Rule

data RV = RV
  { rvRule :: RuleId
  , rvRpos :: ComId
  , rvVar  :: Var}
  deriving (Eq, Ord, Show)




type Var  = String
type Fun  = String

type IPoly = P.Polynomial Int Var
type Term = ATerm Fun Var
type Atom = AAtom Var
type Constraint = AConstraint Var
type Rule = ARule Fun Var
type RV' = (RuleId, ComId)

rules :: Rules -> [Rule]
rules = IM.elems 

rulesIds :: Rules -> [RuleId]
rulesIds = IM.keys

-- | Standard atom encoding.
encodeAtom :: Atom -> SMT.Formula SMT.IFormula
encodeAtom (Eq p1 p2)  = SMT.encodePoly p1 SMT..== SMT.encodePoly p2
encodeAtom (Gte p1 p2) = SMT.encodePoly p1 SMT..>= SMT.encodePoly p2

data SCC a = Trivial a | NonTrivial [a] deriving Show

theSCC :: SCC a -> [a]
theSCC (Trivial a)     = [a]
theSCC (NonTrivial as) = as

instance Functor SCC where
  f `fmap` Trivial a     = Trivial (f a)
  f `fmap` NonTrivial as = NonTrivial (map f as)

instance (PP.Pretty a) => PP.Pretty (SCC a) where
  pretty = PP.pretty . theSCC


ppRV :: RV -> [PP.Doc]
ppRV (RV t i v) = [PP.char '<', PP.int t, PP.comma, PP.int i, PP.comma, PP.string v, PP.char '>']

ppRVs :: Vars -> [(RV, a)] -> (a -> [PP.Doc]) -> PP.Doc
ppRVs vars assocs ppA = PP.table (concatMap ppCol cols)
  where
    ppCol col = zip (repeat PP.AlignRight) (L.transpose (map ppEntry col)) 
    ppEntry (rv,a) = PP.lparen : ppRV rv ++ (comma :ppA a ++ [PP.rparen, PP.space])
    comma = PP.comma PP.<> PP.space

    cols = mkPartition [] vars assocs
    mkPartition acc [] _       = reverse acc
    mkPartition acc (v:vs) es  = mkPartition (a:acc) vs es'
      where (a,es') = L.partition (\(rv,_) -> v == rvVar rv) es

