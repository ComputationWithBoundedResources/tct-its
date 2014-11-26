module Tct.Its.Data.Types where

import qualified Data.Map.Strict as M
import qualified Data.Graph.Inductive as Gr

import qualified Tct.Common.Polynomial as P


type Signature = M.Map Fun Int

data Its = Its
  { _rules           :: Rules
  , _signature       :: Signature
  , _startterm       :: Term

  , _tgraph          :: TGraph
  , _rvgraph         :: Maybe RVGraph

  , _timebounds      :: Timebounds

  , _sizebounds      :: Maybe Sizebounds
  , _localSizebounds :: Maybe LocalSizebounds
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

type RV' = (Int, Int )

type LocalSizebounds = M.Map RV (Cost, Growth)
type Sizebounds = Bounds RV
type Timebounds = Bounds Int


type RuleId = Int
type RVId = Int

type TGraph  = Gr.Gr Rule Int
type RVGraph = Gr.Gr RV ()

data Cost
  = Unknown
  | NPoly IPoly
  deriving (Eq, Show)

data Growth 
  = Max Int      -- ^ > x' = x; x' = y; x' = 3
  | MaxPlus Int  -- ^ > x' = x + 1; x' = y + 3
  | SumPlus Int  -- ^ > x' = y + z; but not x' = x + z
  | Unbounded deriving (Eq,Ord,Show)


