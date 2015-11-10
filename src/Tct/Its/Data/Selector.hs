module Tct.Its.Data.Selector
  ( selAll
  , selUndefineds
  , selNextSCC
  , selFromNextSCC
  , selUpToNextSCC
  , selToNextSCC
  ) where


import qualified Data.IntMap.Strict           as IM
import           Data.List                    (nub)

import           Tct.Its.Data.Problem
import qualified Tct.Its.Data.Timebounds      as TB
import qualified Tct.Its.Data.TransitionGraph as TG
import           Tct.Its.Data.Types


selAll :: Its -> [RuleId]
selAll = IM.keys . irules_

selUndefineds :: Its -> [RuleId]
selUndefineds = TB.nonDefined . timebounds_

selNextSCC :: Its -> [RuleId]
selNextSCC prob = TG.nextSCC (tgraph_ prob) (timebounds_ prob)

selUpToNextSCC :: Its -> [RuleId]
selUpToNextSCC prob = concat $ TG.upToNextSCC (tgraph_ prob) (timebounds_ prob)

selFromNextSCC :: Its -> [RuleId]
selFromNextSCC prob = concat $ TG.fromNextSCC (tgraph_ prob) (timebounds_ prob)

selToNextSCC :: Its -> [RuleId]
selToNextSCC prob = nub . map fst $ TG.incoming(tgraph_ prob) scc
  where scc = selNextSCC prob

