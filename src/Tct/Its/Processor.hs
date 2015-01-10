module Tct.Its.Processor
  (
  module M
  , defaultSDs
  ) where

import Tct.Core.Data                    (StrategyDeclaration (..))

import Tct.Its.Data.Problem             (Its)

import Tct.Its.Processor.Chaining       as M
import Tct.Its.Processor.Empty          as M
import Tct.Its.Processor.PolyRank       as M
import Tct.Its.Processor.Simplification as M
import Tct.Its.Processor.Sizebounds     as M

defaultSDs :: [StrategyDeclaration Its]
defaultSDs = [
  SD emptyDeclaration
  , SD farkasDeclaration
  , SD knowledgePropagationDeclaration
  , SD leafRulesDeclaration
  , SD polyDeclaration
  , SD sizeboundsDeclaration 
  , SD unreachableRulesDeclaration
  , SD unsatRulesDeclaration
  ]

