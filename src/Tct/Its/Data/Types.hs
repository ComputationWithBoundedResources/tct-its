module Tct.Its.Data.Types where

import qualified Data.Map.Strict as M

import qualified Tct.Common.Polynomial as P
import qualified Tct.Core.Common.Pretty as PP


type Signature = M.Map Fun Int

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
type Rules = [(Int, Rule)]



type RV = 
  (Int,  -- ^ Index of the rule
  Int,   -- ^ Index of the rhs
  Var    -- ^ Variable
  )

type RV' = (Int, Int )


type RuleId = Int
type ComId = Int

