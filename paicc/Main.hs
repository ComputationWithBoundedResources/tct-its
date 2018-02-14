{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Tct.Core
import Tct.Core.Data          (abort)
import Tct.Core.Main          (AnswerFormat (..))
import Tct.Its
import Tct.Its.Processor.Lare
import Tct.Its.Strategies

instance Declared Its Its where decls = []

main :: IO ()
main = runIts $
  itsConfig
    { defaultStrategy = maxed .<||> withArgumentFilter maxed
    , putAnswer       = Left TTTACAnswerFormat }

maxed = rank .<|> lare

withArgumentFilter st = force af .>>> st
  where af = withProblem (argumentFilter . unusedFilter)

rank =
  try unsatRules
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> try leafRules
  .>>> try boundTrivialSCCs
  .>>> te (farkas .>>> try knowledgePropagation)
  .>>> abort

lare =
  processor AddSinks
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> processor LooptreeTransformer
  .>>> processor SizeAbstraction
  .>>> processor FlowAbstraction
  .>>> processor LareProcessor
  .>>> abort

