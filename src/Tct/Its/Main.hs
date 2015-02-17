module Main (main) where


import Tct.Core

import Tct.Its.Data.Problem (itsMode)
import Tct.Its.Processor (defaultSDs)


main :: IO ()
main = setMode $ itsMode `withStrategies` defaultSDs

