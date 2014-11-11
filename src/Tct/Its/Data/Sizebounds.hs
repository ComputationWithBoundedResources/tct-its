module Tct.Its.Data.Sizebounds
  (
  Sizebounds
  , initialise
  , module Tct.Its.Data.Bounds
  ) where

import qualified Data.Map.Strict     as M

import           Tct.Its.Data.Bounds
import           Tct.Its.Data.Cost   (Cost)
import           Tct.Its.Data.Rule   (Rule, Var)


type Sizebounds = M.Map (Rule,Int,Var) Cost

initialise :: [Rule] -> Sizebounds
initialise = error "Sizebounds.initialise: yet not implemented"

