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
selAll = IM.keys . _irules

selUndefineds :: Its -> [RuleId]
selUndefineds = TB.nonDefined . _timebounds

selNextSCC :: Its -> [RuleId]
selNextSCC prob = TG.nextSCC (_tgraph prob) (_timebounds prob)

selUpToNextSCC :: Its -> [RuleId]
selUpToNextSCC prob = concat $ TG.upToNextSCC (_tgraph prob) (_timebounds prob)

selFromNextSCC :: Its -> [RuleId]
selFromNextSCC prob = concat $ TG.fromNextSCC (_tgraph prob) (_timebounds prob)

selToNextSCC :: Its -> [RuleId]
selToNextSCC prob = nub . map fst $ TG.incoming(_tgraph prob) scc
  where scc = selNextSCC prob

