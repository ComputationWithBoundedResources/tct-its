module Tct.Its.Data.Timebounds 
  (
  Timebounds
  , initialise
  , module Tct.Its.Data.Bounds 
  ) where


import qualified Data.Map.Strict as M

import Tct.Its.Data.Types
import Tct.Its.Data.Cost
import Tct.Its.Data.Bounds

initialise :: Rules -> Timebounds
initialise rs = M.fromList (zip (fst $ unzip rs) (repeat unknown))

