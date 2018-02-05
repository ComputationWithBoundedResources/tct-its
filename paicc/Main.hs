{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Tct.Core
import Tct.Its
import Tct.Its.Processor.Lare (lare, Program (..))

instance Declared Its Its where decls = [SD lare]

main :: IO ()
main = runIts itsConfig

