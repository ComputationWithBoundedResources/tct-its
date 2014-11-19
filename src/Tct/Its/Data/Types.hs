module Tct.Its.Data.Types where

import qualified Data.Map.Strict as M
import qualified Data.Graph.Inductive as G

import qualified Tct.Common.Polynomial as P


type Signature = M.Map Fun Int

data Its = Its
  { rules           :: Rules
  , signature       :: Signature
  , startterm       :: Term

  , tgraph          :: TGraph
  , rvgraph         :: Maybe RVGraph

  , timebounds      :: Timebounds

  , sizebounds      :: Maybe Sizebounds
  , localSizebounds :: Maybe LocalSizebounds
  } deriving Show


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


type Bounds k = M.Map k Cost

type RV = 
  (Int,  -- ^ Index of the rule
  Int,   -- ^ Index of the rhs
  Var    -- ^ Variable
  )

type LocalSizebounds = Bounds RV
type Sizebounds = Bounds RV
type Timebounds = Bounds Int

type TGraph  = G.Gr () ()
type RVGraph = G.Gr RV ()

data Cost
  = Omega
  | NPoly IPoly
  deriving (Eq, Show)

