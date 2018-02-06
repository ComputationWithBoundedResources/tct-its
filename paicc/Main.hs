{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Tct.Core
import Tct.Its
import Tct.Its.Processor.Lare (lare, Program (..))

instance Declared Its Its where decls = []

main :: IO ()
main = runIts $ itsConfig { defaultStrategy = lare }

