# On the Expressive Power of Languages for Static Variability

[![agda][agda-badge-version-svg]][agda-badge-version-url]

> Note to the OOPSLA Artifact Reviewers:
> This file is intended to be both the artifact's README file, as well as the "artifact documentation" for submission.
> We occasionally add notes like this for information that is relevant only during the review process but not for the broader audience of the artifact in the future.
> In particular, the artifact remains private as of now, to ensure our anonymity to research track PC until our conditionally accepted paper is fully accepted.
> Once our paper is accepted, we will make our artifact publicly available on Github under an open source license and will archive it on Zenodo.
> (When doing so, we will remove all "Note to the OOPSLA Artifact Reviewers" sections from this README.)

> Note to the OOSPLA Artifact Reviewers:
> This is a source code and proof artifact.

This is the supplementary Agda library for our paper _On the Expressive Power of Languages for Static Variability_ conditionally accepted at Object-Oriented Programming, Systems, Languages & Applications 2024 (OOPSLA 2024). 

This library formalizes all results in our paper:

- All formal languages for static software variability presented in our survey (**Section 3 + Table 1**) are formalized as algebraic datatypes.
- The library implements our formal framework for language comparisons, including necessary data structures, theorems, and proofs (**Section 4**).
- This library contains all theorems and proofs to establish the map of variability languages we find by comparing the languages from our survey with our framework (**Section 5**).

  > Note to the OOPSLA Artifact Reviewers: At the time of submission, there were some proofs in our paper that are not marked as formalized in Agda (proof is not marked with a star ★). However, we finished all remaining proofs, so all theorems and proofs from the paper are formalized in Agda by now.

Additionally, our library comes with a small demo.
When run in a terminal, our demo will show a translation roundtrip, showcasing the circle of compilers developed for identifying the map of variability languages (Section 5).

## Hardware Dependencies

There are no specific hardware dependencies.
The library and its demo were tested on standard laptops.

## Kick-the-Tires

This section gives you a short "Getting Started" guide.
For full setup instructions, including detailed instructions on setting up dependencies, see the next section.

The library needs Agda version 2.6.3 (newer version should also work but we did not test them). We tested our setup on Manjaro, NixOS, and Windows Subsystem for Linux (WSL2). The only dependency of our library is the Agda standard library which is shipped as a git submodule within the `agda-stdlib` directory.

### Setup

There are two ways to compile the library and run its small demo.
Either use Nix or install Agda manually.
We recommend using Nix because it creates a sandbox environment with all dependencies satisfied while not affecting your system setup.

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

To install Agda, we recommend following the installation instructions from the [Programming Language Foundations in Agda](https://plfa.github.io/GettingStarted/) book to install GHC, Cabal, and Agda (no need to install the book and the standard-library, which is shipped in the right version in the sub-directory `agda-stdlib` here).

Assuming you have ghc and cabal installed, you can install Agda as follows.

```shell
cabal update
cabal install Agda-2.6.3
```

To test whether this worked or whether your existing installation of Agda has the right version you can check the following command's output:
```shell
> agda --version
Agda version 2.6.3
```

In case of trouble, please head to the detailed step-by-step instructions below or use Nix.

### Compiling the Library and Running the Demo

To test whether your setup is correct, and to run the demo, run make.
Make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.
```shell
make
```
which will compile the library and run its small demo. Alternatively, you may use `nix-build` as explained above.

### Expected Output

Building for the first time (or running `nix-shell`) will take a while because Agda has to build the required dependencies from the standard library (expect ~5-10min). Running the demo will print:

- some translations from option calculus (`OC`) to binary choice calculus (`2CC`),
- some examples for feature structure tree composition, and
- two round-trip translations, following our circle established in the paper: `CCC → ⌈e⌉-CC → 2-CC → 2CC → ADT → VariantList (CaO) → CCC`.
  The first round-trip will translate a trivial choice `D ⟨ l , r ⟩`.
  The second round-trip will translate the sandwich expression from our paper (Expression 1).
  Prepare for a long terminal output because of exponential blowups for `ADT` and `VariantList`. ;)

Note that the demo prints unicode characters to terminal, which should be supported.
There will be a short hint at the beginning of the demo with some test characters.

## Step-by-Step Guide

The "Kick-The-Tires" section above explains all steps for running the demo.
Here, we give additional instructions on how to install the required dependencies such as Nix or Agda.
Note that you do not have to install Agda when you want to use the the Nix setup.

### Installing Nix

To build our library and run the demo with Nix, you must have Nix installed on your system.
How to install Nix, also depends on your operating system.
Head to the [NixOS website](https://nixos.org/download/) and follow the installation instructions for your system.
Follow the download instructions for `Nix: the package manager`, not `NixOS: the Linux distribution`!
Note that Nix is not available for Windows but it can be used from within Windows Subsystem for Linux (WSL2).
To install WSL2, follow the [official instructions](https://learn.microsoft.com/de-de/windows/wsl/install).
In the end, you should be able to open a Linux terminal where you can install Nix by following the instructions for installing Nix on linux from the [NixOS website](https://nixos.org/download/).

### Installing Agda

Following the recommend installation instructions from the [Programming Language Foundations in Agda](https://plfa.github.io/GettingStarted/) book to install GHC, Cabal, and Agda, you basically have to do the following:

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
    cabal install Agda-2.6.4.3
    ```

Detailed installation instructions can also be found [in the official documentation](https://agda.readthedocs.io/en/v2.6.4.3/getting-started/installation.html), too.

3. Finding the standard library: Agda looks for its dependencies in a directory specified by the environment variable `AGDA_DIR`. The provided makefile sets this environment variable temporarily and locally during the build process to the `.libs` directory within this repository. (Your global setup will not be affected). If you want to run `agda` manually, or if you want to work on this project in an editor (e.g., emacs) then you have to set this environment variable to the libs directory in this repository.

    ```shell
    export AGDA_DIR="path/to/this/repository/libs"
    ```

    Beware that setting the variable will overwrite any previously set directory. In that case you might want to overwrite the variable only temporarily while working on this project.

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

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.4.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.4.3
