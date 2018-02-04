{-# Language RecordWildCards #-}
module Tct.Its.Processor.Lare where

-- import qualified Tct.Core.Common.Pretty              as PP
-- import qualified Tct.Core.Common.Xml                 as Xml
-- import qualified Tct.Core.Data                       as T
-- import           Tct.Core

-- import           Tct.Its.Data.Problem
-- import           Tct.Its.Data.Rule
-- import qualified Tct.Its.Data.Timebounds             as TB
-- import qualified Tct.Its.Data.TransitionGraph        as TG
-- import           Tct.Its.Data.Types

import qualified Tct.Its.Processor.Looptree as LT

import qualified Lare.Analysis as LA

-- instance T.Processor CycleManiaProcessor where
--   type ProofObject CycleManiaProcessor = CycleManiaProof
--   type In CycleManiaProcessor          = Its
--   type Out CycleManiaProcessor         = Its
--   type Forking CycleManiaProcessor     = T.Judgement

--   execute CycleMania prob = do
--     let probs = catMaybes $ flip restrictToRuleIds prob `fmap` TG.simpleCycles (irules_ prob)
--     proofs <- mapM entscheide probs
--     let certfn = const $ T.yesNoCert $all (either (const False) (const True)) proofs
--     T.succeedWith0 (CycleManiaProof proofs) certfn




-- toLare :: Its -> L.Top [RuleId] -> 
-- toLare prob tree = go_
--   where
--   vs = domain prob
--   go0 LT.Top rs ts = go_
--   goN LT.Tree{..}  = LA.Tree [] Tree 

-- type Edge = LA.Edge Fun Var

toEdge prob (i,Rule{..}) = 
  let Just lbounds = localSizebounds_ prob in
  LA.edge
    (fun lhs)
    ()
    (fun $ head rhs)

toBound 

-- data ARule f v = Rule
--   { lhs :: ATerm f v
--   , rhs :: [ATerm f v]
--   , con :: [AAtom v] }
--   deriving (Eq, Ord, Show)

-- data Top a = Top a [Tree a]
--   deriving (Show, Functor, Foldable, Traversable)

-- data Tree a
--   = Tree
--   { program     :: a
--   , cutset      :: a
--   , subprograms :: [Tree a] }
--   deriving (Show, Functor, Foldable, Traversable)
