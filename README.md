
# On the Expressive Power of Variability Languages

[![agda][agda-badge-version-svg]][agda-badge-version-url]

This is the supplementary Agda library for our paper _On the Expressive Power of Variability Languages_ submitted to Object-Oriented Programming, Systems, Languages, and Applications 2024 (in PACM PL) (OOPSLA 2024). 

## Setup

The library needs Agda version 2.6.3 (newer version should also work but we did not test them). We tested our setup on Ubuntu (inside windows subsystem for linux (WSL 2)) and Manjaro. The only dependency of this library is the Agda standard library which is shipped as a git submodule within the `agda-stdlib` directory (already contained within the zip file of the supplementary material).

### Installation

To compile the library and run its small demo, you need to have Agda installed.
We recommend following the installation instructions from the [Programming Language Foundations in Agda](https://plfa.github.io/GettingStarted/) book to install GHC, Cabal, and Agda (no need to install the book and the standard-library, which is shipped in the right version in the subdirectory `agda-stdlib` here).

TL;DR: In summary, when following the book, you have to do:

1. Install the GHC compiler (if you have not installed it already) and the cabal build tool for which we recommend using [GHCup](https://www.haskell.org/ghcup/).

    ```shell
    ghcup install ghc 9.2.4
    ghcup install cabal recommended

    ghcup set ghc 9.2.4
    ghcup set cabal recommended
    ```

2. Install Agda

    ```shell
    cabal update
    cabal install Agda-2.6.3
    ```

Detailed installation instructions can also be found [in the official documentation](https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html), too.

3. Finding the standard library: Agda looks for its dependencies in a directory specified by the environment variable `AGDA_DIR`. The provided makefile sets this environment variable during the build process to the `.libs` directory within this repository. If you want to run `agda` manually, or if you want to work on this project in an editor (e.g., emacs) then you have to set this environment variable to the libs directory in this repository.

    ```shell
    export AGDA_DIR="path/to/this/repository/libs"
    ```

    Beware that setting the variable will overwrite any previously set directory. In that case you might want to overwrite the variable only temporarily while working on this project.

### Compiling the Library and Running the Demo

To test whether you setup Agda correctly, and to run this libraries demo, run make:
```shell
make
```
which will compile the library and run its small demo.

Building for the first time will take a while because Agda has to build the required dependencies from the standard library (expect ~5-10min). Running the demo will print some translations of core to binary choice calculus, and translations from option calculus to binary choice calculus. When running the demo, make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.

## Project Structure

The library is organized as follows:

- [src/Framework](src/Framework) contains the definitions of our formal framework, defined in Section 4 in our paper.
  Here, you can find the core data types in [Definitions.lagda.md](src/Framework/Definitions.lagda.md).
  Soundness and completeness are defined in the [Properties](src/Framework/Properties) sub-directory.
  Definitions for expressiveness and other relations are in the [Relation](src/Framework/Relation) sub-directory.
  Theorems for proving completeness, soundness, and expressiveness based on their relationships (Section 4.5) are within the [Proof](src/Framework/Proof) sub-directory.
- [src/Lang](src/Lang) contains instantiations of particular variability languages.
- [src/Translation](src/Translation) contains translations between variability languages, such as the translation of option calculus to binary choice calculus in [OC-to-2CC.lagda.md](src/Translation/OC-to-2CC.lagda.md) (Section 5.3 in our paper).
- [src/Test](src/Test) contains definitions of unit tests for translations and some experiments that are run, when running the library.

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3
