-- | This module re-export useful top-level definitions.
module Tct.Its (module M) where

import Tct.Its.Config       as M (runIts, ItsConfig, itsConfig)
import Tct.Its.Data.Problem as M (Its (..), ItsStrategy, ItsDeclaration)
import Tct.Its.Strategies   as M

