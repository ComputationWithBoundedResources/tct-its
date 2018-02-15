module Main (main) where

import Tct.Core
import Tct.Its

instance Declared Its Its where decls = itsDeclarations

main :: IO ()
main = runIts itsConfig

