module Tct.Its.Data.Timebounds 
  (
  Timebounds
  , initialise
  , module Tct.Its.Data.Bounds 
  ) where


import qualified Data.Map.Strict as M

import qualified Tct.Core.Common.Pretty as PP

import Tct.Its.Data.Rule (Rule)
import Tct.Its.Data.Cost
import Tct.Its.Data.Bounds

type Timebounds = M.Map Rule Cost

initialise :: [Rule] -> Timebounds
initialise rs = M.fromList (zip rs (repeat omega))

instance PP.Pretty Timebounds where
  pretty = ppBounds PP.pretty

