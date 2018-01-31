module Main (main) where

import Tct.Core
import Tct.Its
import Tct.Its.Processor.Looptree (cyclemania, looptree)

instance Declared Its Its where decls = SD looptree : SD cyclemania : itsDeclarations

main :: IO ()
main = runIts itsConfig

