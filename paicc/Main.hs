{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Tct.Core
import Tct.Core.Data (abort)
import Tct.Core.Main (AnswerFormat(..))
import Tct.Its
import Tct.Its.Strategies
import Tct.Its.Processor.Lare

instance Declared Its Its where decls = []

main :: IO ()
main = runIts $ 
  itsConfig 
    { defaultStrategy = lare
    , putAnswer       = Left TTTACAnswerFormat }



lare =
  processor AddSinks
  .>>> try unsatPaths
  .>>> try unreachableRules
  .>>> processor LooptreeTransformer
  .>>> processor SizeAbstraction
  .>>> processor FlowAbstraction
  .>>> processor LareProcessor
  .>>> abort
