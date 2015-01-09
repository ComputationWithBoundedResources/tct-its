module Tct.Its.Processor where

import Tct.Core.Data (StrategyDeclaration(..))

import Tct.Its.Data.Problem (Its)

import Tct.Its.Processor.Empty
import Tct.Its.Processor.PolyRank
import Tct.Its.Processor.Simplification
import Tct.Its.Processor.Sizebounds

defaultSDs :: [StrategyDeclaration Its]
defaultSDs = 
  [ SD emptyDeclaration
  , SD farkasDeclaration
  , SD polyDeclaration
  , SD leafRulesDeclaration
  , SD unsatRulesDeclaration
  , SD unreachableRulesDeclaration
  , SD sizeboundsDeclaration ]

