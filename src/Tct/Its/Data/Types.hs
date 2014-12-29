module Tct.Its.Data.Types where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L

import qualified Tct.Common.Polynomial as P
import qualified Tct.Core.Common.Pretty as PP


type Signature = M.Map Fun Int

restrictSignature :: S.Set Fun -> Signature -> Signature
restrictSignature fs = M.filterWithKey (\k _ -> k `S.member` fs)

instance PP.Pretty Signature where
  pretty sig = PP.semiBraces $ map (\(f,i) -> PP.tupled [PP.pretty f, PP.pretty i]) (M.toList sig)


type Var  = String
type Fun  = String
type IPoly = P.Polynomial Int Var

data Term = Term 
  { fun  :: Fun 
  , args :: [IPoly]
  } deriving (Eq, Ord, Show)

data Atom
  = Eq IPoly IPoly
  | Gte IPoly IPoly
  deriving (Eq, Ord, Show)

type Constraint = [Atom]

data Rule = Rule
  { lhs :: Term
  , rhs :: [Term]
  , con :: Constraint }
  deriving (Eq, Ord, Show)


type Vars  = [Var]
type RuleId = Int
type Rules = IM.IntMap Rule



data RV = RV
  { rvRule :: Int
  , rvRpos :: Int
  , rvVar  :: Var}
  deriving (Eq, Ord, Show)

type RV' = (Int, Int )


type ComId = Int




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

