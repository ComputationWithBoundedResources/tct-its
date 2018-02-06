{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Tct.Core
import Tct.Core.Data (abort)
import Tct.Its
import Tct.Its.Strategies
import Tct.Its.Processor.Lare

instance Declared Its Its where decls = []

main :: IO ()
main = runIts $ itsConfig { defaultStrategy = lare }



lare =
  try unsatPaths
  .>>> try unreachableRules
  .>>> processor AddSinks
  .>>> processor LooptreeTransformer
  .>>> processor SizeAbstraction
  .>>> processor FlowAbstraction
  .>>> processor LareProcessor
  .>>> abort
