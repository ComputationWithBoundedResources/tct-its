module Tct.Its.Data.Timebounds
  (
  Timebounds
  , initialise
  , module Tct.Its.Data.Bounds
  ) where


import qualified Data.Map.Strict          as M

import           Tct.Core.Common.SemiRing (one)
import           Tct.Its.Data.Bounds
import           Tct.Its.Data.Cost        (unknown)
import           Tct.Its.Data.Types       (RuleId)

type Timebounds = Bounds RuleId

-- | @initialise all starts@ sets the complexity of @all@ to 'Unknown' and the complexity of @starts@ to @1@.
initialise :: [RuleId] -> [RuleId] -> Timebounds
initialise allids = foldl (\tbounds' i -> M.insert i one tbounds') tbounds
  where tbounds = M.fromList (zip allids (repeat unknown))

