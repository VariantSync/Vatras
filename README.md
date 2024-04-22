# On the Expressive Power of Languages for Static Variability

[![agda][agda-badge-version-svg]][agda-badge-version-url]

This is the supplementary Agda library for our paper _On the Expressive Power of Languages for Static Variability_ submitted to Object-Oriented Programming, Systems, Languages & Applications 2024 (OOPSLA 2024). 

## Setup

The library needs Agda version 2.6.3 (newer version should also work but we did not test them). We tested our setup on Ubuntu (inside windows subsystem for linux (WSL 2)), Manjaro, and NixOS. The only dependency of this library is the Agda standard library which is shipped as a git submodule within the `agda-stdlib` directory (already contained within the zip file of the supplementary material).

### Installation

There are two ways to compile the library and run its small demo.
Either use Nix, or install Agda manually.
We recommend using Nix.

#### Installation via Nix

When you have Nix installed on your system, you can get access to all necessary development utilities by navigating to this directory and then simply opening a Nix shell
``` shell
nix-shell
```
Alternatively, the demo can be compiled and run directly using
``` shell
nix-build
./result/bin/EPVL
```

To use this repository as a library in you own project, you can use `agda.withPackages`:
```nix
agda = nixpkgs.agda.withPackages [
  nixpkgs.agdaPackages.standard-library
  (import /path/to/this/git/repository {
    pkgs = nixpkgs;
  })
];
```
Though, not required, we recommend to use the [nixpkgs pin](nix/sources.json) created using [niv](https://github.com/nmattia/niv) provided in this respository to minimize version conflicts.

#### Manual Installation
We recommend following the installation instructions from the [Programming Language Foundations in Agda](https://plfa.github.io/GettingStarted/) book to install GHC, Cabal, and Agda (no need to install the book and the standard-library, which is shipped in the right version in the subdirectory `agda-stdlib` here).

TL;DR: In summary, when following the book, you have to do:

0. Install [GHCup](https://www.haskell.org/ghcup/), which we recommend for installing `ghc` and `cabal`. 
   ```shell 
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh 
   ```

1. Install the GHC compiler (if you have not installed it already) and the cabal build tool with [GHCup](https://www.haskell.org/ghcup/).

    ```shell
    ghcup install ghc 9.2.4
    ghcup install cabal recommended

    ghcup set ghc 9.2.4
    ghcup set cabal recommended
    ```

2. Install Agda (this may take a while).

    ```shell
    cabal update
    cabal install Agda-2.6.3
    ```

Detailed installation instructions can also be found [in the official documentation](https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html), too.

3. Finding the standard library: Agda looks for its dependencies in a directory specified by the environment variable `AGDA_DIR`. The provided makefile sets this environment variable temporarily, and locally during the build process to the `.libs` directory within this repository. (Your global setup will not be affected). If you want to run `agda` manually, or if you want to work on this project in an editor (e.g., emacs) then you have to set this environment variable to the libs directory in this repository.

    ```shell
    export AGDA_DIR="path/to/this/repository/libs"
    ```

    Beware that setting the variable will overwrite any previously set directory. In that case you might want to overwrite the variable only temporarily while working on this project.

### Compiling the Library and Running the Demo

To test whether you setup Agda correctly, and to run this libraries demo, run make:
```shell
make
```
which will compile the library and run its small demo. Alternatively, you may use `nix-build` as explained above.

Building for the first time will take a while because Agda has to build the required dependencies from the standard library (expect ~5-10min). Running the demo will print:

- some translations from option calculus (`OC`) to binary choice calculus (`2CC`),
- some examples for feature structure tree composition, and
- two round-trip translations, following our circle established in the paper: `CCC → ⌈e⌉-CC → 2-CC → 2CC → ADT → VariantList (CaO) → CCC`.
  The first round-trip will translate a trivial choice `D ⟨ l , r ⟩`.
  The second round-trip will translate the sandwich expression from our paper (Expression 1).
  Prepare for a long terminal output because of exponential blowups for `ADT` and `VariantList`. ;)

When running the demo, make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.
Also, the demo prints unicode characters to terminal, which should be supported.
There will be a short hint at the beginning of the demo with some test characters.

## Project Structure

The library is organized as follows:

- The [src/Framework](src/Framework) directory contains the definitions of our formal framework, defined in Section 4 in our paper.
  - [VariabilityLanguage.lagda.md](src/Framework/VariabilityLanguage.lagda.md) defines variability languages and their denotational semantics.
  - Soundness and completeness are defined in the [Properties](src/Framework/Properties) sub-directory.
  - Definitions for expressiveness and configuration equivalence are in the [Relation](src/Framework/Relation) sub-directory.
  - Theorems for proofs for free (Section 4.4) are within the [Proof](src/Framework/Proof) sub-directory, including several more interesting theorems, which did not fit into the paper.
- [src/Lang](src/Lang) contains definitions of particular variability languages (Section 3).
- [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md) contains an overview of our case study (Section 5) to compare existing variability languages. The compilers can be found in the [src/Translation/Lang](src/Translation/Lang) sub-directory.
- [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md) implements the theory of indexed sets with various operators and equational reasoning.
- [src/Test/Experiments/RoundTrip.agda](src/Test/Experiments/RoundTrip.agda) implements the round-trip for our demo, including our sandwich running example. This file may serve as an entry point and example on how to run the compilers implemented in the library.

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3
