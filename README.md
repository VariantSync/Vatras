﻿# Vatras - On the Expressive Power of Languages for Static Variability

[![Check the Agda files](https://github.com/pmbittner/Vatras/actions/workflows/check.yml/badge.svg)](https://github.com/pmbittner/Vatras/actions/workflows/check.yml)
[![agda][agda-badge-version-svg]][agda-badge-version-url]
[![License](https://img.shields.io/badge/License-GNU%20LGPLv3-blue)](LICENSE.LGPL3)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.13502454.svg)](https://doi.org/10.5281/zenodo.13502454)

[![Preprint](https://img.shields.io/badge/OOPSLA'24-Preprint-purple)](https://github.com/SoftVarE-Group/Papers/raw/main/2024/2024-OOPSLA-Bittner.pdf)
[![Paper](https://img.shields.io/badge/OOPSLA'24-Paper-purple)](https://doi.org/10.1145/3689747)
[![Slides](https://img.shields.io/badge/OOPSLA'24-Slides-purple)](https://github.com/SoftVarE-Group/Slides/raw/main/2024/2024-10-25-OOPSLA-Variability-Languages.pdf)
[![Talk](https://img.shields.io/badge/OOPSLA'24-Talk-purple)](https://www.youtube.com/watch?v=kHYEHSHLffU&t=12713)
[![Distinguished-Artifact](https://img.shields.io/badge/OOPSLA'24-Distinguished%20Artifact-gold)](https://2024.splashcon.org/track/splash-2024-oopsla-artifacts#Chair-s-Report)

<img padding="10" align="right" src="https://www.acm.org/binaries/content/gallery/acm/publications/artifact-review-v1_1-badges/results_reproduced_v1_1.png" alt="ACM Results Reproduced" width="114" height="113"/>
<img padding="10" align="right" src="https://www.acm.org/binaries/content/gallery/acm/publications/artifact-review-v1_1-badges/artifacts_evaluated_reusable_v1_1.png" alt="ACM Artifacts Evaluated Reusable" width="114" height="113"/>

Vatras is the supplementary Agda library for our OOPSLA'24 paper:

> _On the Expressive Power of Languages for Static Variability_. Paul M. Bittner, Alexander Schultheiß, Benjamin Moosherr, Jeffrey M. Young, Leopoldo Teixeira, Eric Walkingshaw, Parisa Ataei, Thomas Thüm. Object-Oriented Programming, Systems, Languages & Applications, 2024 (**OOPSLA 2024**).

This library formalizes all results in our paper:

- All **formal languages for static software variability** presented in our survey (Section 3 + Table 1) are formalized as algebraic datatypes.
- The library implements our **formal framework for language comparisons**, including necessary data structures, theorems, and proofs (Section 4).
- This library contains **all theorems and proofs to establish the map of variability languages we find** by comparing the languages from our survey with our framework (Section 5).

Additionally, our library comes with a small **demo**, and **tutorials** for getting to know the library and for formalizing your own variability languages (see "Tutorials" section below).
When run in a terminal, our demo will show a translation roundtrip, showcasing the circle of compilers developed for identifying the map of variability languages (Section 5).

## Overview: What is Static Variability and What is Vatras?

Vatras is a library to study and compare meta-languages for specifying variability in source code and data.
Some software systems are configurable _before_ they are compiled, i.e., statically.
A common way example for implementing static variability is by conditional compilation, as for example possible with the C preprocessor.
For instance, the following [code snippet from the Linux kernel](https://github.com/torvalds/linux/blob/e271ed52b344ac02d4581286961d0c40acc54c03/include/linux/console.h#L479-L486)

```C
#ifdef CONFIG_DEBUG_LOCK_ALLOC
extern bool console_srcu_read_lock_is_held(void);
#else
static inline bool console_srcu_read_lock_is_held(void)
{
  return 1;
}
#endif
```

replaces the function `console_srcu_read_lock_is_held` with a default implementation in case a particular feature should be debugged.
Essentially, the code snippet above does not denote a single `C` program but two `C` programs, each using one of two alternatives for the function `console_srcu_read_lock_is_held`.

To model and analyze static variability, researchers have formalized various formal languages, including formalisms for conditional compilation.
For example, the _choice calculus_ is a small language to formalize conditional compilation in terms of a singly syntactic term, referred to as a _choice_.
A choice `F ⟨ l , r ⟩` specifies two alternatives `l` and `r` for a feature or configuration option `F`.
Encoding the example above in choice calculus yields

```
CONFIG_DEBUG_LOCK_ALLOC ⟨ 
  extern bool console_srcu_read_lock_is_held(void);
,
  static inline bool console_srcu_read_lock_is_held(void)
  {
    return 1;
  }
⟩
```

Apart from source code, static configuration processes emerge in many other areas, including our daily lives. 
For instance, some restaurants offer your to configure your meal.
Sticking to the choice calculus, we may for example specify a configurable sandwich that _always_ has bread 🍞 and cheese, _maybe_ has salad 🥗 (expressed as a choice between Salad 🥗 and an empty value `ε`), _either_ has a meat 🍖 or falafel 🧆 patty, and has _any_ combination of mayonnaise 🥚 and ketchup 🍅 as follows:

```
🍞-< 
  Salad⟨ 🥗, ε ⟩,
  🧀,
  Patty⟨ 🍖, 🧆 ⟩,
  Sauce⟨ ε, 🥚, 🍅, 🍅🥚 ⟩
  >-
```
where the Y-brackets of the outer expression `🍞-< ... >-` denote that the ingredients go _within_ the bread (i.e., we build a tree where the ingredients are sub-expressions of bread).

The goal of Vatras is to formalize and _compare_ languages for static variabilty.
To this end, we formalize the syntax and semantics of the choice calculus, some of its dialects, and many more formal languages for static variability.
For instance, writing out the above sandwich expression in our Agda formalization of the choice calculus, closely resembles the original expressions (most boilerplate comes from explicit list syntax):

``` agda
sandwich : CCC Feature ∞ Artifact
sandwich =
  "🍞" -<
       "Salad" ⟨ leaf "🥗" ∷ leaf "ε" ∷ [] ⟩
    ∷  leaf "🧀"
    ∷  "Patty" ⟨ leaf "🍖" ∷ leaf "🧆" ∷ [] ⟩
    ∷  "Sauce" ⟨ leaf "ε"  ∷ leaf "🥚" ∷ leaf "🍅" ∷ leaf "🍅🥚" ∷ [] ⟩
    ∷ []
  >-
  where
    leaf : String → CCC Feature ∞ Artifact
    leaf a = a -< [] >-
```

We may configure our sandwich in terms of the semantics `⟦_⟧` for choice calculus.
The semantics is a function takes a configuration as input to produce a variant.
For our sandwich example, a configuration decides for each configuration option `Salad`, `Patty`, and `Sauce` which alternative to pick.
A variant is a sandwich without any conditional elements left (i.e., a term without choices).
From a configuration, we can derive the respective sandwich variant, and we can use Agda to prove that the semantics derive the variant we expect:

``` agda
config : Feature → ℕ
config "Salad" = 0
config "Patty" = 1
config "Sauce" = 2
config _ = 0

config-makes-falafel-ketchup-sandwich :
  ⟦ sandwich ⟧ config ≡
    "🍞" -<
         leaf "🥗"
      ∷  leaf "🧀"
      ∷  leaf "🧆"
      ∷  leaf "🍅"
      ∷ []
    >-
config-makes-falafel-ketchup-sandwich = refl
```

Vatras enables semantic comparisons of variability languages based on a meta-theory centered around the three fundamental yet unexplored properties of completeness, soundness, and expressiveness.
Completeness serves as a lower bound (i.e., a language can express at least a given semantic domain),
soundness serves as an upper bound (i.e., a language can express at most a given semantic domain),
and expressiveness serves as a relative comparison (i.e., a language can express at least the semantic domain of another language).
Proofs of these properties come as _encodings_ for completeness (i.e., a function that creates a variational expression from a set of variants), _enumerations_ for soundness (i.e., a function that enumerates all variants denoted by a variational expression), and _compilers_ between languages for expressiveness.
Vatras includes a range of proofs of these properties for existing languages as explained in our respective paper.
As a showcase, Vatras will show a roundtrip translation of the configurable sandwich specification above when you run it.
Details on the features implemented in Vatras, including tutorials for integrating new languages, can be found in the **Reusability Guide** below.

## Kick-the-Tires

This section gives you a short "Getting Started" guide.
For detailed instructions on setting up dependencies, see the next section.
We tested our setup on Manjaro, NixOS, Windows Subsystem for Linux (WSL2), and we also tested the Docker setup on Windows 11 and macOS Ventura 13.0.1 (22A400) on an Apple M1 Pro.

> In case of problems, there is a "Troubleshooting" section at the bottom of this file.

### Setup
Clone the library and its submodules to a directory of your choice:
```shell 
git clone --recursive https://github.com/VariantSync/Vatras.git
```

There are **three alternative ways** to compile the library and run its small demo.
**Either use Nix, Docker, or install Agda manually.**
In general, we **recommend Nix** because it creates a sandbox environment with all dependencies satisfied while not affecting your system setup (as does Docker), as well as giving you the opportunity to adapt and reuse the library in your own Agda projects (Docker requires to rebuild an image after every change).

- For **Windows** users, we recommend Docker. If you are familiar with Windows Subsystem for Linux (WSL2), you may safely use the other alternatives in WSL2, too. To install WSL2, follow the [official instructions](https://learn.microsoft.com/de-de/windows/wsl/install). 
- For **Mac** users, we recommend Nix or Docker. (We experienced problems with installing Agda manually.)
- For **Linux** users, any alternative is fine but we recommend Nix for the reasons mentioned above.

There are no other software requirements apart from having either Nix, Docker, or Agda installed, depending on which alternative you choose..
The only dependency of our library is the Agda standard library which is shipped as a git submodule within the `agda-stdlib` directory and is taken care of automatically by our [makefile](makefile).

Note that building for the first time (or running `nix-shell`) will take a while because Agda has to build the required dependencies from the standard library (expect ~5-10min and a lot of terminal output).

#### Alternative 1: Setup via Nix

The installation of Nix depends on your operating system. Head to the [NixOS website](https://nixos.org/download/) and follow the installation instructions for your system. Follow the download instructions for `Nix: the package manager`, not `NixOS: the Linux distribution`! Note that Nix is not directly available for Windows but it can be used from within Windows Subsystem for Linux (WSL2). When you open a WSL2 terminal terminal, you can install Nix by following the instructions for installing Nix on linux from the [NixOS website](https://nixos.org/download/).

When you have Nix installed on your system, open a terminal, navigate to this directory, and then simply open a Nix shell by typing
```shell
nix-shell
```
Make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.
To compile the library and run the demo, simply run make:
```shell
make
```
The expected output is explained in detail in the Step-by-Step guide below.

Alternatively, the demo can be compiled locally to `./result/bin`.
```shell
nix-build
```
and then run via:
```shell
./result/bin/Vatras
```

#### Alternative 2: Setup via Docker

How to install Docker depends on your operating system. **For Windows or Mac**, you can find download and installation instructions [here](https://www.docker.com/get-started). **On Linux**, installing Docker depends on your distribution. The chances are high that Docker is part of your distributions package database. Docker's [documentation](https://docs.docker.com/engine/install/) contains instructions for common distributions.

Once you have installed Docker, start the Docker daemon.
**On Windows**, open the search bar using the 'Windows Key' and search for 'Docker' or 'Docker Desktop'.
**On Linux**, the docker daemon typically runs automatically, so there is nothing to do; otherwise, start Docker's service using your service manager (e.g., with `systemd`, execute `sudo systemctl start docker`).
More detailed instructions on starting the deamon are given [here](https://docs.docker.com/config/daemon/start/) on the docker website.

Afterwards, open a terminal and navigate to this repository's directory (the directory containing this README.md).
First, you must create the docker image:
``` shell
docker build -t vatras .
```

Optionally, you may verify that the image was created successfully by running
```shell
docker images
```
and checking that an image called `vatras` is listed.

You can then run the demo by running the Docker image:
```shell
docker run -t vatras
```

#### Alternative 3: Manual Setup

The library needs Agda version 2.6.4.3 (newer version should also work but we did not test them).
There are different ways to install Agda.
Following the [Agda book's installation instructions], we recommend using [GHCup][ghcup] to install GHC, Cabal, and Agda as follows (You may skip steps for tools you have already installed but there might be compatibility errors with some versions):

0. Install [GHCup][ghcup], which we recommend for installing `ghc` and `cabal`. 
   ```shell 
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh 
   ```

1. Install the GHC compiler and the cabal build tool with [GHCup][ghcup].

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

   To test whether the installation worked or whether your existing installation of Agda has the right version you can check the following command's output:
   ```shell
   > agda --version
   Agda version 2.6.4.3
   ```
   
In case of confusion or trouble, we recommend to check the [official installation instructions](https://agda.readthedocs.io/en/v2.6.4.3/getting-started/installation.html), or follow the Getting-Started guide in the [Programming Language Foundations in Agda][plfa] book, or use the Nix setup, or check the troubleshooting instructions at the bottom of this file.

To test whether your setup is correct, and to run the demo you may use our makefile.
Make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.
Then run
```shell
make
```
which will compile the library and run its small demo.
The expected output is explained in detail in the Step-by-Step guide below.

## Step-by-Step Guide

The "Kick-The-Tires" section above basically explains all necessary steps to get the library up and running.
Here, we give additional instructions on the expected output and how to play with other demo inputs.
For using the library once you finished the setup, please have a look at the later _Reusability Guide_, which, among other
information, includes an overview of the library, notes on our mechanized proofs, and tutorials for getting to know the library.

### How does the demo know which standard library to use?

Agda looks for its dependencies in a directory specified by the environment variable `AGDA_DIR`. The provided [makefile](makefile) sets this environment variable temporarily and locally during the build process to the `.libs` directory within this repository. (Your global setup will not be affected). If you want to run `agda` manually, or if you want to work on this project in an editor (e.g., emacs) then you have to set this environment variable to the libs directory in this repository.

```shell
export AGDA_DIR="path/to/this/repository/libs"
```

Beware that setting the variable will overwrite any previously set directory. In that case you might want to overwrite the variable only temporarily while working on this project.

### Expected Output

The demo will print a long terminal output of about 1250 lines.
A copy of the expected output can be found in the [expected-output.txt](expected-output.txt).

First, the demo prints unicode characters to terminal, as a test for you to see whether your terminal supports unicode.
The first lines should look like this.

```
It's dangerous to go alone! Take this unicode to see whether your terminal supports it:
  ₙ ₁ ₂ 𝕃 ℂ 𝔸 ⟦ ⟧ ⟨ ⟩ ❲❳
... but now on to the demo
```

The actual demo will then print:

- some translations from option calculus (`OC`) to binary choice calculus (`2CC`),
- some examples for feature structure tree composition, and
- two round-trip translations, following our circle established in the paper: `CCC → ⌈e⌉-CC → 2-CC → 2CC → ADT → VariantList (CaO) → CCC`.
  The first round-trip will translate a trivial choice `D ⟨ l , r ⟩`.
  The second round-trip will translate the sandwich expression from our paper (Expression 1).
  Prepare for a long terminal output because of exponential blowups for `ADT` and `VariantList`. ;)

## Reusability Guide

Our library was designed to be reusable in other research endeavors or tools for studying or analyzing static variability.
In particular, our library provides,

- **formalizations of common variability languages** as algebraic data types, including their abstract syntax and semantics (see Section 3 in our paper), and sometimes functions or proofs of their properties (e.g., for algebraic decision trees, we have implemented a dead-branch elimination and proved it correct). Previously, most of these languages were only defined on paper. These formalizations can be reused to implement variational analyses or more practice-oriented variability languages. (Our formalization might even serve as teaching material for courses on software variability in the future.)
- **proven-to-be correct compilers**, which translate common variability languages into each other (see Section 5 in our paper). The compilers can be reused to, for example, translate datasets or inputs to reuse analysis formulated based on a particular language to all other languages which are less or equally expressive.
- a means to conduct **basic sanity checks** for language designers, such as soundness or completeness. Language designers can relate new languages to existing ones with only one or two translations with respective proofs without having to compare to each language individually. 
- a reusable implementation of **indexed sets** that can be used to talk about subsets of types in terms of functions.
- a small **pretty-printing** library which we use for the terminal output of our demo.
- a range of **tutorials** guiding you through the process of creating your own language and comparing it to existing ones, eventually concluding completeness and soundness either for free or by yourself. In the future, these tutorials might even serve as teaching material for courses on software variability.

### Overview

The library is organized as follows:

- The [src/Vatras/Framework](src/Vatras/Framework) directory contains the definitions of our formal framework, defined in Section 4 in our paper.
  - [VariabilityLanguage.agda](src/Vatras/Framework/VariabilityLanguage.agda) defines variability languages and their denotational semantics.
  - Soundness and completeness are defined in the [Properties](src/Vatras/Framework/Properties) sub-directory.
  - Definitions for expressiveness and configuration equivalence are in the [Relation](src/Vatras/Framework/Relation) sub-directory.
  - Theorems for proofs for free (Section 4.4) are within the [Proof](src/Vatras/Framework/Proof) sub-directory, including several additional interesting theorems, which did not fit into the paper.
- [src/Vatras/Lang](src/Vatras/Lang) contains definitions of particular variability languages (Section 3).
- [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md) contains an overview of our case study (Section 5) to compare existing variability languages.
  - [src/Vatras/Translation/Lang](src/Vatras/Translation/Lang) contains the compilers and the resulting expressiveness proofs in one file per language pair and direction (e.g., `2CC-to-ADT` implements the translation from binary choice calculus to algebraic decision trees and its correctness proof).
  - Further sub-directories of [src/Vatras/Translation/Lang](src/Vatras/Translation/Lang) facilitate intra-language compilers (i.e., compilers from a language to itself). For example, [src/Vatras/Translation/Lang/ADT/DeadElim.agda](src/Vatras/Translation/Lang/ADT/DeadElim.agda) implements a compiler from `ADT` to `ADT` that eliminates any dead branches, and additionally generates a proof that the returned `ADT` does not have any dead branches anymore.
- [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md) implements the theory of indexed sets with various operators and equational reasoning.
- [src/Vatras/Test](src/Vatras/Test) contains our unit test infrastructure (or better: unit _proofs_) as well as some example expressions for some languages.
- [src/Vatras/Test/Experiments/RoundTrip.agda](src/Vatras/Test/Experiments/RoundTrip.agda) implements the round-trip for our demo, including our sandwich running example. This file may serve as an entry point and example on how to run the compilers implemented in the library.
- [src/Vatras/Tutorial](src/Vatras/Tutorial) contains tutorials for getting to know the library (explained in more detail below).
- [src/Vatras/Show/Lines.agda](src/Vatras/Show/Lines.agda) implements a small pretty-printer, which we use for the demo's output.

### Tutorials

To extend or reuse the library, we offer a range of tutorials in the [Tutorials module](src/Vatras/Tutorial).
These tutorials are literate Agda files with holes for you to fill in.
Hence, when trying the tutorials you can directly check your definitions to be type-correct with Agda in a suitable editor (e.g., Emacs or VS Code) and you can navigate the framework.
The tutorials might also serve as copy-and-paste-templates for new definitions.

1. [The New Language Tutorial](src/Vatras/Tutorial/A_NewLanguage.lagda.md) explains how to define a new variability language, including syntax, semantics, and configuration.
2. [The Translation Tutorial](src/Vatras/Tutorial/B_Translation.lagda.md) explains how to compile/translate your language to another existing language and proving correctness.
3. [The Proofs Tutorial](src/Vatras/Tutorial/C_Proofs.lagda.md) explains how to prove completeness, soundness, and expressiveness, and how you can use your compiler to do so.

We recommend following the tutorials in order.

### Documentation

The code base is documented thoroughly, in terms of inline comments for most definitions.
For some of the crucial files or proof steps, we use literate Agda (mostly Markdown) to explain proofs step-by-step.
In terms of tutorials (see above), we provide a detailed introduction to the library and its central definitions.
We refrained from providing documentation in terms of a separate website because commonly, Agda is best navigated, explored, and read from within a suitable editor (typically Emacs, Vim, or VS Code).
  
### Changing the Demo Input

To adapt the demo, you can implement your own experiments and add them to the list of experiments to run at the top of the [Main](src/Vatras/Main.agda) file.
If you simply want to change the inputs of existing experiments, you can change the list of inputs for each experiment in the list of experiments as well.
In particular, you may add new inputs to the round-trip translation by adding your own example core choice calculus expression (`CCC`) to the `examples` list at the bottom of the [RoundTrip module](src/Vatras/Test/Experiments/RoundTrip.agda).
You may define your own expression by adding a new definition like this, where `ex-new` is the name of your example, `"The new example"` is its title, and where `{!!}` is an Agda hole which you can fill in with an abstract syntax tree of a core choice calculus expression:
```agda
ex-new : Example (CCC.CCC Feature ∞ Artifact)
ex-new = "The new example" ≔ {!!}
```
Then add your new list to the `examples` list at the bottom of the file.

### Using our library in your own Agda projects

#### Alternative 1: Installation via Nix

When using Nix, you can use this repository as a library in you own project, by using `agda.withPackages`:
```nix
agda = nixpkgs.agda.withPackages [
  nixpkgs.agdaPackages.standard-library
  (import /path/to/this/git/repository {
    pkgs = nixpkgs;
  })
];
```
Though, not required, we recommend to use the [nixpkgs pin](nix/sources.json) created using [niv](https://github.com/nmattia/niv) provided in this repository to minimize version conflicts.

#### Alternative 2: Manual installation

After downloading this library, you can register it by appending the path of [Vatras.agda-lib](Vatras.agda-lib) to the file `$AGDA_DIR/libraries`, creating it if necessary.
If the environment variable `AGDA_DIR` is unset, it defaults to `~/.agda` on unix-like systems and `C:\Users\USERNAME\AppData\Roaming\agda` or similar on Windows.
After registering this library on your system, you can use it in your project by stating `Vatras` as a dependency in your Agda library file.
An Agda library file has the suffix `.agda-lib` and is usually contained in the root directory of your project.
Its content, including the dependency to Vatras, should include the following:

```
name: YOUR-PROJECT-NAME
depend: Vatras
include: SOME/PATH/IN/YOUR/PROJECT
```

For details about Agda's library management, please have a look at [Agda's packaging guide](https://agda.readthedocs.io/en/v2.6.4.3/tools/package-system.html).

### Notes on Mechanized Proofs

#### Paper-to-Library Correspondence

Our Agda formalization exhaustively formalizes all definitions, theorems, and proofs from our paper.
The following table shows where each of the definitions, theorems, and proofs from the paper are formalized in this library.

| statement       | notation in paper                 | name in our Agda Library                                           | file                                                                                                               | notes                                                                                                                                                              |
|-----------------|-----------------------------------|--------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Section 1       | contribution: a map of languages  |                                                                    | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Section 2       | running example                   |                                                                    | [src/Vatras/Test/Experiments/RoundTrip.agda](src/Vatras/Test/Experiments/RoundTrip.agda)                           |                                                                                                                                                                    |
| Table 1         |                                   |                                                                    | [src/Vatras/Lang/All.agda](src/Vatras/Lang/All.agda)                                                               | This file only reexports the language definitions. Use the go-to-definition functionality of your editor for easy exploration.                                     |
|                 | Core Choice Calculus              | `CCC`                                                              | [src/Vatras/Lang/CCC.lagda.md](src/Vatras/Lang/CCC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | Binary Choice Calculus            | `2CC`                                                              | [src/Vatras/Lang/2CC.lagda.md](src/Vatras/Lang/2CC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | Algebraic Decision Trees          | `ADT`                                                              | [src/Vatras/Lang/ADT.agda](src/Vatras/Lang/ADT.agda)                                                               |                                                                                                                                                                    |
|                 | Gruler's Language                 | `Gruler`                                                           | [src/Vatras/Lang/Gruler.agda](src/Vatras/Lang/Gruler.agda)                                                         |                                                                                                                                                                    |
|                 | Option Calculus                   | `WFOC`, `OC`                                                       | [src/Vatras/Lang/OC.lagda.md](src/Vatras/Lang/OC.lagda.md)                                                         | In contrast to the paper, WFOC duplicates the artifact constructor to enforce the existence of a top-level artifact.                                               |
|                 | Feature Structure Trees           | `FST`                                                              | [src/Vatras/Lang/FST.agda](src/Vatras/Lang/FST.lagda.md)                                                           |                                                                                                                                                                    |
|                 | Clone-and-Own (List of Variants)  | `VariantList`                                                      | [src/Vatras/Lang/VariantList.lagda.md](src/Vatras/Lang/VariantList.lagda.md)                                       |                                                                                                                                                                    |
| Definition 4.1  | Indexed Set                       | `IndexedSet`                                                       | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
| Definition 4.3  | Indexed Set Inclusion ⋿           | `_∈_`                                                              | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
|                 | Subset ⊑                          | `_⊆_`, `_⊆[_]_`                                                    | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         | In contrast to `_⊆_`, `_⊆[_]_` requires an explicit mapping between the indices of the two indexed sets which can be useful information.                           |
|                 | Equivalence ≅                     | `_≅_`, `_≅[_][_]`_                                                 | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         | The difference between `_≅_` and `_≅[_][_]_` is the same as between `_⊆_` and `_⊆[_]_`.                                                                            |
| Corollary 4.5   | ⊑ is a partial order              | `⊆-IsIndexedPartialOrder`,  `⊆[]-refl`, `⊆[]-antisym`, `⊆[]-trans` | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
|                 | ≅ is an equivalence relation      | `≅-IsIndexedEquivalence`, `≅[]-refl`, `≅[]-sym`, `≅[]-trans`       | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
| Definition 4.6  | Finite Indexed Set                |                                                                    |                                                                                                                    | We actually only need finite and non-empty indexed sets and do not define finite indexed sets separately.                                                          |
| Definition 4.8  | Non-empty Indexed Set             | `empty`                                                            | [src/Vatras/Data/IndexedSet.lagda.md](src/Vatras/Data/IndexedSet.lagda.md)                                         | The library definition is a predicate that ensures an indexed set to be non-empty.                                                                                 |
| Definition 4.9  | Variant Generator                 | `VariantGenerator`                                                 | [src/Vatras/Framework/VariantGenerator.agda](src/Vatras/Framework/VariantGenerator.agda)                           | This is the finite and non-empty indexed set definition mentioned above.                                                                                           |
| Definition 4.10 | Semantic Domain                   | `VariantGenerator`                                                 | [src/Vatras/Framework/VariantGenerator.agda](src/Vatras/Framework/VariantGenerator.agda)                           | In contrast to a variant generator, the semantic domain is the type of variant generators instead of its elements.                                                 |
| Definition 4.11 | configuration language 𝐶          | `ℂ`                                                                | [src/Vatras/Framework/Definitions.agda](src/Vatras/Framework/Definitions.agda)                                     |                                                                                                                                                                    |
| Definition 4.12 | variability language 𝐿            | `𝔼`                                                                | [src/Vatras/Framework/Definitions.agda](src/Vatras/Framework/Definitions.agda)                                     |                                                                                                                                                                    |
| Definition 4.13 | ⟦.⟧                               | `𝔼-Semantics`                                                      | [src/Vatras/Framework/VariabilityLanguage.agda](src/Vatras/Framework/VariabilityLanguage.agda)                     |                                                                                                                                                                    |
|                 |                                   | `VariabilityLanguage`                                              | [src/Vatras/Framework/VariabilityLanguage.agda](src/Vatras/Framework/VariabilityLanguage.agda)                     | VariabilityLanguage is a bundle of 𝔼, 𝕂 and 𝔼-Semantics.                                                                                                           |
| Definition 4.15 | Complete(𝐿)                       | `Complete`                                                         | [src/Vatras/Framework/Properties/Completeness.lagda.md](src/Vatras/Framework/Properties/Completeness.lagda.md)     |                                                                                                                                                                    |
| Definition 4.16 | Sound(𝐿)                          | `Sound`                                                            | [src/Vatras/Framework/Properties/Soundness.lagda.md](src/Vatras/Framework/Properties/Soundness.lagda.md)           |                                                                                                                                                                    |
| Definition 4.17 | ⪰                                 | `_≽_`                                                              | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≡                                 | `_≋_`                                                              | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≻                                 | `_≻_`                                                              | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Corollary 4.18  | ⪰ is a partial order              | `≽-IsPartialOrder`                                                 | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≡ is an equivalence relation      | `≋-IsEquivalence`                                                  | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Definition 4.19 | 𝑀 ⇾ 𝐿                             |                                                                    |                                                                                                                    | We only model correct compilers.                                                                                                                                   |
| Definition 4.20 | 𝑀 ⇾ 𝐿 correct                     | `LanguageCompiler`                                                 | [src/Vatras/Framework/Compiler.agda](src/Vatras/Framework/Compiler.agda)                                           |                                                                                                                                                                    |
| Theorem 4.21    | 𝑀 ⇾ 𝐿 ⇒ 𝐿 ⪰ 𝑀                     | `expressiveness-from-compiler`                                     | [src/Vatras/Framework/Relation/Expressiveness.lagda.md](src/Vatras/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Theorem 4.22    | Complete(M) ∧ L ≽ M ⇒ Complete(L) | `completeness-by-expressiveness`                                   | [src/Vatras/Framework/Proof/ForFree.lagda.md](src/Vatras/Framework/Proof/ForFree.lagda.md)                         |                                                                                                                                                                    |
| Theorem 4.23    | Sound(L) ∧ L ≽ M ⇒ Sound(M)       | `soundness-by-expressiveness`                                      | [src/Vatras/Framework/Proof/ForFree.lagda.md](src/Vatras/Framework/Proof/ForFree.lagda.md)                         |                                                                                                                                                                    |
| Theorem 4.24    | Complete(L) ∧ Sound(M) ⇒ L ≽ M    | `expressiveness-by-completeness-and-soundness`                     | [src/Vatras/Framework/Proof/ForFree.lagda.md](src/Vatras/Framework/Proof/ForFree.lagda.md)                         |                                                                                                                                                                    |
| Figure 3        |                                   |                                                                    | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         | This file mostly reexports expressiveness results and applies transitivity and the above theorems. It serves as a nice entry point to explore most of our results. |
| Theorem 5.1     | 𝑛-CC                              | `NCC`                                                              | [src/Vatras/Lang/NCC.lagda.md](src/Vatras/Lang/NCC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | 𝑛-CC ⪰ CCC                        | `NCC≽CCC`                                                          | [src/Vatras/Translation/Lang/CCC-to-NCC.agda](src/Vatras/Translation/Lang/CCC-to-NCC.agda)                         |                                                                                                                                                                    |
|                 | clamp                             | `Exact.translate`                                                  | [src/Vatras/Translation/Lang/CCC-to-NCC.agda](src/Vatras/Translation/Lang/CCC-to-NCC.agda)                         |                                                                                                                                                                    |
|                 | shrink₂                           | `shrinkTo2Compiler`                                                | [src/Vatras/Translation/Lang/NCC/ShrinkTo2.agda](src/Vatras/Translation/Lang/NCC/ShrinkTo2.agda)                   |                                                                                                                                                                    |
|                 | grow                              | `growCompiler`                                                     | [src/Vatras/Translation/Lang/NCC/Grow.agda](src/Vatras/Translation/Lang/NCC/Grow.agda)                             |                                                                                                                                                                    |
| Theorem 5.3     | ADT ≽ 2CC                         | `ADT≽2CC`                                                          | [src/Vatras/Translation/Lang/2CC-to-ADT.agda](src/Vatras/Translation/Lang/2CC-to-ADT.agda)                         |                                                                                                                                                                    |
| Corollary 5.5   | CCC ≡ 2CC ≡ ADT ≡ 𝑛-CC            | `CCC≋NCC`, `NCC≋2CC`, and `2CC≋ADT`                                | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.6     | Complete(CaO)                     | `VariantList-is-Complete`                                          | [src/Vatras/Lang/VariantList.lagda.md](src/Vatras/Lang/VariantList.lagda.md)                                       |                                                                                                                                                                    |
| Theorem 5.7     | Sound(CaO)                        | `VariantList-is-Sound`                                             | [src/Vatras/Lang/VariantList.lagda.md](src/Vatras/Lang/VariantList.lagda.md)                                       |                                                                                                                                                                    |
| Theorem 5.8     | CaO ≽ ADT                         | `VariantList≽ADT`                                                  | [src/Vatras/Translation/Lang/ADT-to-VariantList.agda](src/Vatras/Translation/Lang/ADT-to-VariantList.agda)         |                                                                                                                                                                    |
| Theorem 5.10    | CCC ≽ CaO                         | `CCC≽VariantList`                                                  | [src/Vatras/Translation/Lang/VariantList-to-CCC.lagda.md](src/Vatras/Translation/Lang/VariantList-to-CCC.lagda.md) |                                                                                                                                                                    |
| Corollary 5.11  | CCC is complete and sound         | `CCC-is-complete`, `CCC-is-sound`                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | 2CC is complete and sound         | `2CC-is-complete`, `2CC-is-sound`                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | ADT is complete and sound         | `ADT-is-complete`, `ADT-is-sound`                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | 𝑛-CC is complete and sound        | `NCC-is-complete`, `NCC-is-sound`                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.12    | 2CC ≽ OC                          | `2CC≽OC`                                                           | [src/Vatras/Translation/Lang/OC-to-2CC.lagda.md](src/Vatras/Translation/Lang/OC-to-2CC.lagda.md)                   |                                                                                                                                                                    |
| Corollary 5.13  | Sound(OC)                         | `OC-is-sound`                                                      | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.14    | ¬Complete(OC)                     | `OC-is-incomplete`                                                 | [src/Vatras/Lang/OC.lagda.md](src/Vatras/Lang/OC.lagda.md)                                                         |                                                                                                                                                                    |
| Theorem 5.15    | 2CC ≻ OC                          | `2CC≻WFOC`                                                         | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.16    | ¬Complete(FST)                    | `FST-is-incomplete`                                                | [src/Vatras/Lang/FST.lagda.md](src/Vatras/Lang/FST.lagda.md)                                                       |                                                                                                                                                                    |
| Theorem 5.17    | OC ⋡ FST                          | `WFOC⋡FST`                                                         | [src/Vatras/Translation/Lang/FST-to-OC.lagda.md](src/Vatras/Translation/Lang/FST-to-OC.lagda.md)                   |                                                                                                                                                                    |
| Theorem 5.18    | FST ⋡ OC                          | `FSTL⋡WFOCL`                                                       | [src/Vatras/Translation/Lang/OC-to-FST.agda](src/Vatras/Translation/Lang/OC-to-FST.agda)                           |                                                                                                                                                                    |
| Corollary 5.19  | FST ⋡ CaO                         | `FST⋡VariantList`                                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.20    | CaO ≽ FST                         | `VariantList≽FST`                                                  | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Corollary 5.21  | Sound(FST)                        | `FST-is-sound`                                                     | [src/Vatras/Translation/LanguageMap.lagda.md](src/Vatras/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |

Some formalizations in the library differ slightly from their in-paper-representation:

- A few definitions and proofs in this library generalize over the type of variants `V : 𝕍`.
In the paper, this type is fixed to rose trees (see Definition 3.1, trees where each node can have any number of children), which we also formalized in [src/Vatras/Framework/Variants.agda](src/Vatras/Framework/Variants.agda) as type `Rose`.
This generalization allows us to also formalize variability languages that
(1) have other variant types such as Gruler's language (see [src/Vatras/Lang/Gruler.agda](src/Vatras/Lang/Gruler.agda), Section 3.6 in the paper), or
(2) are independent of the variant type, such as [clone and own](src/Vatras/Lang/VariantList.lagda.md) (Section 5.2 in the paper).
- Also generalizing over the annotation language `F : 𝔽` was rather easy in the paper (Section 3.3) but requires to carry around that `𝔽` explicitly in Agda in definitions and theorems a lot.

#### Frameworks and Dependencies

Except for the Agda standard-library, this library has no dependencies, as explained in the setup instructions above.
In particular, this means we do not rely on other proof frameworks.

#### Proof Structure, Organization, and Documentation

Our library consists of many proofs. Their organization into multiple files is presented in the Overview section, and the
Paper-to-Library table above.
Proofs are documented inline via comments in the code (also see the Documentation section above).

#### On Axioms and Assumptions

Our library, does not use any of the following assumptions or axioms in central parts of the code:

1. **no** additional axioms via `postulate` (e.g., no extensionality or excluded middle)
2. **no** termination macros (`{-# TERMINATING -#}`). All functions and proofs are proven to terminate (for proofs this means they use well-founded induction or are non-cyclic).
3. **no** unfinished proofs (i.e., there are no holes `{! !}`).

Of course, there are three exceptions to this.

##### Exception 1

For the [tutorials](src/Vatras/Tutorial) (see above), we deliberately use many holes.
These holes are intended to be exercises for someone who is working through the tutorial.
We also use a terminating macro here to avoid sized types to keep the tutorial simple.
The place where we use the macro is proven to terminate throughout the rest
of the library multiple times, by using sized types.

##### Exception 2

For termination checking, we use sized types, which currently have [known inconsistencies](https://github.com/agda/agda/issues?q=is%3Aopen+label%3Afalse+sized+types).
The risks of using them in inconsistent ways are [often accepted](https://github.com/agda/agda/issues/4908) because they can simplify proofs substantially.
We came to the same conclusion and tried our best to use them without interaction with more complicated language features to reduce the likelihood of encountering an inconsistency.
In particular, we use sized types only in a very basic, inductive way and:
- We do not use coinductive data types ([#7178](https://github.com/agda/agda/issues/7178), [#1946](https://github.com/agda/agda/issues/1946), [#1201](https://github.com/agda/agda/issues/1201)).
- We do not use `Size<` ([#6002](https://github.com/agda/agda/issues/6002)).
- We do not compare `Size` for equality ([#2820](https://github.com/agda/agda/issues/2820)).

##### Exception 3

For a non-crucial part of our framework, we included four postulates, which assume that two primitive operations from the standard library are invertible:

- converting `String`s to lists of characters and vice versa,
- converting characters to natural numbers and vice versa.

These postulates can be found in [src/Vatras/Util/String.agda](src/Vatras/Util/String.agda).
We believe these postulates to be reasonable because strings are commonly _defined_ as lists of characters, and because characters are usually encoded as natural numbers in text encodings (e.g., UTF-8).
We use these axioms as an example, to prove that we can simplify annotations `String × ℕ` to just `String`, by turning a pair `s , n` into a String representation `s ++ "." ++ show n`.
This simplification only exists to beautify theorems (so they do not have to mention the pair) and align them more closely to our paper but our results would remain the same without that simplification.
In fact, some of these postulates are an open issue [#6119](https://github.com/agda/agda/issues/6119) in the Agda implementation.

### Limitations

- The library currently only supports abstract syntax for all languages. There are no parsers, so it is not yet possible to read in files or strings of concrete syntax. This is not a claim of the paper though and would just be a nice additional feature.

## Troubleshooting

### Errors mentioning `MAlonzo`

If you see an error similar to this one
```
.../src/MAlonzo/Code/Vatras/Data/IndexedSet.hs:1705:3: error:
    Not in scope:
      type constructor or class ‘MAlonzo.Code.Agda.Primitive.T_Level_14’
    Perhaps you meant ‘MAlonzo.Code.Agda.Primitive.T_Level_18’ (imported from MAlonzo.Code.Agda.Primitive)
    Module ‘MAlonzo.Code.Agda.Primitive’ does not export ‘T_Level_14’.
     |
1705 |   MAlonzo.Code.Agda.Primitive.T_Level_14 ->
     |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
there might be corrupt build files. Simply run `make clean`.

### Errors mentioning `commitAndReleaseBuffer`

If you see an error similar to this one
```
It's dangerous to go alone! Take this unicode to see whether your terminal supports it:
   Vatras: <stdout>: commitAndReleaseBuffer: invalid argument (cannot encode character '\8345')
```
there might be a problem with your terminal settings.
In particular, this error is caused by the [Haskell runtime failing to detect UTF-8 support of your terminal](https://gitlab.haskell.org/ghc/ghc/-/issues/8118).
This might be caused by your terminal not actually supporting Unicode, or, more likely, misdetection of the Unicode capabilities of your terminal.
Simply set the environment variable `LC_ALL` to `C.UTF-8` by, for example, running `export LC_ALL=C.UTF-8` before running Vatras, to force Unicode detection.

### Unexpected or weird symbols

The first lines the demo prints should be
```
It's dangerous to go alone! Take this unicode to see whether your terminal supports it:
  ₙ ₁ ₂ 𝕃 ℂ 𝔸 ⟦ ⟧ ⟨ ⟩ ❲❳
... but now on to the demo.
```
The second line should not be empty, nor should it contain Unicode replacement characters or characters with accents.
Instead, it should contain mathematical symbols.
There are two possible causes if you do not see the mathematical symbols:

- The font you are using is missing the required symbols.
  In this case you can use a different font as a fallback or switch to a different font altogether.
  A common font supporting all required symbols is Symbola.

- Your terminal does not support UTF-8 correctly.
  In this case you have to switch to a different terminal.

### Docker fails due to signal 9

If you see an error like
```
 failed due to signal 9 (Killed)
------
Dockerfile:19
--------------------
  17 |
  18 |     # Verify all proofs and build the demo.
  19 | >>> RUN nix-build
  20 |
  21 |     # Copy the demo with all runtime dependencies (ignoring build-time dependencies)
--------------------
ERROR: failed to solve: process "/bin/sh -c nix-build" did not complete successfully: exit code: 100
```
during a Docker build, you might have encountered an out of memory issue.
Try to rerun the same command after closing other applications which might comsume a lot of RAM.
In some cases it may also be necessary to disable some kind of out-of-memory killer (also known as OOM killer or OOM deamon) but use this option with caution.

### Failed to read library file ./libs/../agda-stdlib/standard-library.agda-lib.
The following error may occur when executing `make` after a manual setup: 
```
Failed to read library file ./libs/../agda-stdlib/standard-library.agda-lib.
Reason: ./libs/../agda-stdlib/standard-library.agda-lib: openBinaryFile: does not exist (No such file or directory)
make: *** [makefile:15: build] Error 42
```
This error indicates that the `agda-stdlib` git submodule has not been set up correctly. 
Executing `git submodule update --init` in the root of the repository should fix the problem. 

## Where does the library name 'Vatras' come from?

The name Vatras is (of course) an acronym, which stands for _VAriability language TRAnslationS_.
Besides, Vatras is a water mage in the classic german RPG [Gothic II](https://almanach.worldofgothic.de/index.php/Vatras), who stems from the city of Varant, which almost sounds like _Variant_.
Vatras is praying to the god Adanos, who brings some kind of equality or balance loosely speaking.

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.4.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.4.3
[ghcup]: https://www.haskell.org/ghcup/
[plfa]: https://plfa.github.io/GettingStarted/
