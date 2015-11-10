-- | This module re-exports Tct.Its.Processor.*.
module Tct.Its.Processors (module M) where

import Tct.Its.Data.Selector                            as M
import Tct.Its.Processor.Chaining                       as M
import Tct.Its.Processor.Empty                          as M
import Tct.Its.Processor.PathAnalysis                   as M
import Tct.Its.Processor.PolyRank                       as M
import Tct.Its.Processor.Simplification                 as M
import Tct.Its.Processor.Sizebounds                     as M
import Tct.Its.Processor.TransitionPredicateAbstraction as M

