-- | This module re-exports Tct.Its.Processor.*.
module Tct.Its.Processor
  (
  module M
  , wellformed
  , defaultDecls
  ) where


import Tct.Core
import Tct.Its.Data.Problem

import Tct.Its.Data.Selector                            as M
import Tct.Its.Processor.Chaining                       as M
import Tct.Its.Processor.Empty                          as M
import Tct.Its.Processor.PathAnalysis                   as M
import Tct.Its.Processor.PolyRank                       as M
import Tct.Its.Processor.Simplification                 as M
import Tct.Its.Processor.Sizebounds                     as M
import Tct.Its.Processor.TransitionPredicateAbstraction as M


defaultDecls :: [StrategyDeclaration Its Its]
defaultDecls = [
  SD emptyDeclaration
  , SD farkasDeclaration
  , SD knowledgePropagationDeclaration
  , SD leafRulesDeclaration
  , SD pathAnalysisDeclaration
  , SD polyDeclaration
  , SD sizeboundsDeclaration
  , SD unreachableRulesDeclaration
  , SD unsatRulesDeclaration
  ]


wellformed :: ItsStrategy
wellformed = withProblem $ \prob -> 
  when (not $ validate prob) (failing "Problem is not well-fomed.")

