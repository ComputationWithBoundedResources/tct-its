##tct-its
This package is part of the _Tyrolean Complexity Tool (TcT)_ and provides
automatic complexity analysis of _Integer Transition Systems (ITSs)_.

This repository provides the `tct-its` library as well as the `tct-trs` executable.

##Requirements

Executables:
  * [Glasgow Haskell Compiler, version 7.10](http://www.haskell.org/ghc/) 
  * [yices, version 2.3](http://yices.csl.sri.com/)

Other packages
  * [slogic](https://github.com/ComputationWithBoundedResources/slogic/)
  * [tct-core](https://github.com/ComputationWithBoundedResources/tct-core/)
  * [tct-common](https://github.com/ComputationWithBoundedResources/tct-common/)

The tool is only tested under GNU/Linux.

###Installation

####Using Stack
We recommend using [stack](https://github.com/commercialhaskell/stack) with the accompanied `stack.yaml` file.
To build and install the package run following command:

```bash
stack install
```

####Using Cabal
For building via `cabal/cabal-install`, make sure that you have [ghc](http://www.haskell.org/ghc/) and [cabal](http://www.haskell.org/cabal/).
To build and install the package run following commands:

```bash
mkdir tct-bundle
cd tct-bundle
git clone https://github.com/ComputationWithBoundedResources/slogic
git clone https://github.com/ComputationWithBoundedResources/tct-core
git clone https://github.com/ComputationWithBoundedResources/tct-common
git clone https://github.com/ComputationWithBoundedResources/tct-its
cabal install **/*.cabal
```

###Example Usage
The installation provides an executable `tct-its`.

```bash
tct-its examples/insertsort.its
```

For full options, run `tct-its --help`.

