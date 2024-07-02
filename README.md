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

> Note to the OOPSLA Artifact Reviewers:
> Some links in this document only work from within the repository.
> Some links are relative, pointing to specific files or directories which are unavailable
> when reading this documentation as a standalone file.

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
We tested our setup on Manjaro, NixOS, Windows Subsystem for Linux (WSL2), and we also tested the Docker setup on Windows 11.

> In case of problems, there is a "Troubleshooting" section at the bottom of this file.

### Setup

There are **three alternative ways** to compile the library and run its small demo.
**Either use **Nix, Docker, or install Agda manually.**
We **recommend Nix** because it creates a sandbox environment with all dependencies satisfied while not affecting your system setup (as does Docker), as well as giving you the opportunity to adapt and reuse the library in your own Agda projects (Docker requires to rebuild an image after every change).
If you just want to run the demo or if you are on **Windows** and don't want to install WSL2, we recommend Docker.

There are no other software requirements apart from having either Nix, Docker, or Agda installed.
The only dependency of our library is the Agda standard library which is shipped as a git submodule within the `agda-stdlib` directory and is taken care of automatically by our [makefile](makefile).

Note that building for the first time (or running `nix-shell`) will take a while because Agda has to build the required dependencies from the standard library (expect ~5-10min and a lot of terminal output).

#### Alternative 1: Setup via Nix

The installation of Nix depends on your operating system. Head to the [NixOS website](https://nixos.org/download/) and follow the installation instructions for your system. Follow the download instructions for `Nix: the package manager`, not `NixOS: the Linux distribution`! Note that Nix is not directly available for Windows but it can be used from within Windows Subsystem for Linux (WSL2). To install WSL2, follow the [official instructions](https://learn.microsoft.com/de-de/windows/wsl/install). In the end, you should be able to open a Linux terminal where you can install Nix by following the instructions for installing Nix on linux from the [NixOS website](https://nixos.org/download/).

When you have Nix installed on your system, you can get access to all necessary development utilities by opening a terminal, navigating to this directory, and then simply opening a Nix shell by typing
```shell
nix-shell
```
Alternatively, the demo can be compiled and run directly using
```shell
nix-build
./result/bin/EPVL
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
docker build -t epvl .
```

Optionally, you may verify that the image was created successfully by running
```shell
docker images
```
and checking that an image called `epvl` is listed.

You can then run the demo by running the image:

```shell
docker run -t epvl
```

#### Alternative 3: Manual Setup

The library needs Agda version 2.6.3 (newer version should also work but we did not test them).
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
   Agda version 2.6.3
   ```
   
In case of confusion or trouble, we recommend to check the [official installation instructions](https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html), or follow the Getting-Started guide in the [Programming Language Foundations in Agda][plfa] book, or use the Nix setup.

### Compiling the Library and Running the Demo

To test whether your setup is correct, and to run the demo you may use our makefile (except for the docker setup which requires to run the image as explained above).
Make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.
If you are using Nix, make sure to be in the `nix-shell` as described above.
Then run
```shell
make
```
which will compile the library and run its small demo.
Alternatively, you may use `nix-build` as explained above.
The demo will then print a range of translations of variational expressions to the terminal.
The expected output is explained in detail in the Step-by-Step guide below.

## Step-by-Step Guide

The "Kick-The-Tires" section above basically explains all necessary steps to get the library up and running.
Here, we give additional instructions on the expected output and how to play with other demo inputs.

### How does the demo know which standard library to use?

Agda looks for its dependencies in a directory specified by the environment variable `AGDA_DIR`. The provided [makefile](makefile) sets this environment variable temporarily and locally during the build process to the `.libs` directory within this repository. (Your global setup will not be affected). If you want to run `agda` manually, or if you want to work on this project in an editor (e.g., emacs) then you have to set this environment variable to the libs directory in this repository.

    ```shell
    export AGDA_DIR="path/to/this/repository/libs"
    ```

    Beware that setting the variable will overwrite any previously set directory. In that case you might want to overwrite the variable only temporarily while working on this project.

### Expected Output

First, the demo prints unicode characters to terminal, as a test for you to see whether your terminal supports unicode.
The first lines should look like this.

```shell
It's dangerous to go alone! Take this unicode to see whether your terminal supports it:
  ₙ ₁ ₂ 𝕃 ℂ 𝔸 ⟦ ⟧ ⟨ ⟩ ❲❳
... but now on to the demo.
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

- The [src/Framework](src/Framework) directory contains the definitions of our formal framework, defined in Section 4 in our paper.
  - [VariabilityLanguage.lagda.md](src/Framework/VariabilityLanguage.lagda.md) defines variability languages and their denotational semantics.
  - Soundness and completeness are defined in the [Properties](src/Framework/Properties) sub-directory.
  - Definitions for expressiveness and configuration equivalence are in the [Relation](src/Framework/Relation) sub-directory.
  - Theorems for proofs for free (Section 4.4) are within the [Proof](src/Framework/Proof) sub-directory, including several additional interesting theorems, which did not fit into the paper.
- [src/Lang](src/Lang) contains definitions of particular variability languages (Section 3).
- [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md) contains an overview of our case study (Section 5) to compare existing variability languages.
  - [src/Translation/Lang](src/Translation/Lang) contains the compilers and the resulting expressiveness proofs in one file per language pair and direction (e.g., `2CC-to-ADT` implements the translation from binary choice calculus to algebraic decision trees and its correctness proof).
  - Further sub-directories of [src/Translation/Lang](src/Translation/Lang) facilitate intra-language compilers (i.e., compilers from a language to itself). For example, [src/Translation/Lang/ADT/DeadElim.agda](src/Translation/Lang/ADT/DeadElim.agda) implements a compiler from `ADT` to `ADT` that eliminates any dead branches, and additionally generates a proof that the returned `ADT` does not have any dead branches anymore.
- [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md) implements the theory of indexed sets with various operators and equational reasoning.
- [src/Test](src/Test) contains our unit test infrastructure (or better: unit _proofs_) as well as some example expressions for some languages.
- [src/Test/Experiments/RoundTrip.agda](src/Test/Experiments/RoundTrip.agda) implements the round-trip for our demo, including our sandwich running example. This file may serve as an entry point and example on how to run the compilers implemented in the library.
- [src/Tutorial](src/Tutorial) contains tutorials for getting to know the library (explained in more detail below).
- [src/Show/Lines.agda](src/Show/Lines.agda) implements a small pretty-printer, which we use for the demo's output.

### Tutorials

To extend or reuse the library, we offer a range of tutorials in the [Tutorials module](src/Tutorial).
These tutorials are literate Agda files with holes for you to fill in.
Hence, when trying the tutorials you can directly check your definitions to be type-correct with Agda in a suitable editor (e.g., Emacs or VS Code) and you can navigate the framework.
The tutorials might also serve as copy-and-paste-templates for new definitions.

1. [The New Language Tutorial](src/Tutorial/A_NewLanguage.lagda.md) explains how to define a new variability language, including syntax, semantics, and configuration.
2. [The Translation Tutorial](src/Tutorial/B_Translation.lagda.md) explains how to compile/translate your language to another existing language and proving correctness.
3. [The Proofs Tutorial](src/Tutorial/C_Proofs.lagda.md) explains how to proof completeness, soundness, and expressiveness, and how you can use your compiler to do so.

We recommend following the tutorials in order.

### Documentation

The code base is documented thoroughly, in terms of inline comments for most definitions.
For some of the crucial files or proof steps, we use literate Agda (mostly markdown) to explain proofs step-by-step.
In terms of tutorials (see above), we provide a detailed introduction to the library and its central definitions.
We refrained from providing documentation in terms of a separate website because commonly, Agda is best navigated, explored, and read from within a suitable editor (typically Emacs, Vim, or VS Code).
  
### Changing the Demo Input

To adapt the demo, you can implement your own experiments and add them to the list of experiments to run at the top of the [Main](src/Main.agda) file.
If you simply want to change the inputs of existing experiments, you can change the list of inputs for each experiment in the list of experiments as well.
In particular, you may add new inputs to the round-trip translation by adding your own example core choice calculus expression (`CCC`) to the `examples` list at the bottom of the [RoundTrip module](src/Test/Experiments/RoundTrip.agda).
You may define your own expression by adding a new definition like this, where `ex-new` is the name of your example, `"The new example"` is its title, and where `{!!}` is an Agda hole which you can fill in with an abstract syntax tree of a core choice calculus expression:
```agda
ex-new : Example (CCC.CCC Feature ∞ Artifact)
ex-new = "The new example" ≔ {!!}
```
Then add your new list to the `examples` list at the bottom of the file.

### Using our library in your own Agda projects

When using Nix, you can use this repository as a library in you own project, by using `agda.withPackages`:
```nix
agda = nixpkgs.agda.withPackages [
  nixpkgs.agdaPackages.standard-library
  (import /path/to/this/git/repository {
    pkgs = nixpkgs;
  })
];
```
Though, not required, we recommend to use the [nixpkgs pin](nix/sources.json) created using [niv](https://github.com/nmattia/niv) provided in this respository to minimize version conflicts.

### Notes on Mechanized Proofs

> Note to the OOPSLA Artifact Reviewers:
> Here is where we explain everything regarding the guidelines on proof artifacts.

#### Paper-to-Library Correspondence

Some formalizations in the library differ slightly from their in-paper-representation.

- The reason is that in this library, we generalized over the type of variants `V`.
In the paper, this type is fixed to rose trees (see Definition 3.1), which we also formalized in [src/Framework/Variants.agda](src/Framework/Variants.agda) as type `Rose`.
Many proofs do not require variants to be rose trees though but instead only require that variants have a constructor for artifacts `a -< e , ... , e >-` (which `Rose` [does](src/Framework/Variants.agda)).
This generalization allows us to also formalize other variability languages such as Gruler's language (see [src/Lang/Gruler.agda](src/Lang/Gruler.agda) within our library.
- Also generalizing over the annotation language `𝔽` was rather easy in the paper but requires to carry around that `𝔽` in Agda a lot.

The following table shows where each of the definitions, theorems, and proofs from the paper are formalized in this library. Note that this table is exhaustive.

| statement       | notation in paper                 | name in our Agda Library                                           | file                                                                                                 | notes                                                                                                                                                              |
|-----------------|-----------------------------------|--------------------------------------------------------------------|------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Section 1       | contribution: a map of languages  |                                                                    | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Section 2       | running example                   |                                                                    | [src/Test/Experiments/RoundTrip.agda](src/Test/Experiments/RoundTrip.agda)                           |                                                                                                                                                                    |
| Table 1         |                                   |                                                                    | [src/Lang/All/Generic.agda](src/Lang/All/Generic.agda)                                               | This file only reexports the language definitions. Use the go-to-definition functionality of your editor for easy exploration.                                     |
|                 | Core Choice Calculus              | `CCC`                                                              | [src/Lang/CCC.lagda.md](src/Lang/CCC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | Binary Choice Calculus            | `2CC`                                                              | [src/Lang/2CC.lagda.md](src/Lang/2CC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | Algebraic Decision Trees          | `ADT`                                                              | [src/Lang/ADT.agda](src/Lang/ADT.agda)                                                               |                                                                                                                                                                    | -- TODO NADT uses different constructor names than in the paper
|                 | Gruler's Language                 | `Gruler`                                                           | [src/Lang/Gruler.agda](src/Lang/Gruler.agda)                                                         |                                                                                                                                                                    | -- TODO different constructor names than in the paper
|                 | Option Calculus                   | `WFOC`, `OC`                                                       | [src/Lang/OC.lagda.md](src/Lang/OC.lagda.md)                                                         | In contrast to the paper, WFOC duplicates the artifact constructor to enforce the existence of a top-level artifact.                                               |
|                 | Feature Structure Trees           | `FST`                                                              | [src/Lang/FST.agda](src/Lang/FST.agda)                                                               |                                                                                                                                                                    |
|                 | Clone-and-Own (List of Variants)  | `VariantList`                                                      | [src/Lang/VariantList.agda](src/Lang/VariantList.agda)                                               |                                                                                                                                                                    |
| Definition 4.1  | Indexed Set                       | `IndexedSet`                                                       | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
| Definition 4.3  | Indexed Set Inclusion ⋿           | `_∈_`                                                              | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
|                 | Subset ⊑                          | `_⊆_`, `_⊆[_]_`                                                    | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         | In contrast to `_⊆_`, `_⊆[_]_` requires an explicit mapping between the indices of the two indexed sets which can be useful information.                           |
|                 | Equivalence ≅                     | `_≅_`, `_≅[_][_]`_                                                 | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         | The difference between `_≅_` and `_≅[_][_]_` is the same as between `_⊆_` and `_⊆[_]_`.                                                                            |
| Corollary 4.5   | ⊑ is a partial order              | `⊆-IsIndexedPartialOrder`,  `⊆[]-refl`, `⊆[]-antisym`, `⊆[]-trans` | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
|                 | ≅ is an equivalence relation      | `≅-IsIndexedEquivalence`, `≅[]-refl`, `≅[]-sym`, `≅[]-trans`       | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         |                                                                                                                                                                    |
| Definition 4.6  | Finite Indexed Set                |                                                                    | [                                                                                                    | We](                                                                                                                                                               | We) actually only need finite and non-empty indexed sets and do not define finite indexed sets separately. |
| Definition 4.8  | Non-empty Indexed Set             | `empty`                                                            | [src/Data/IndexedSet.lagda.md](src/Data/IndexedSet.lagda.md)                                         | The library definition is a predicate that ensures an indexed set to be non-empty.                                                                                 |
| Definition 4.9  | Variant Map                       | `VMap`                                                             | [src/Framework/VariantMap.agda](src/Framework/VariantMap.agda)                                       | This is the finite and non-empty indexed set definition mentioned above.                                                                                           |
| Definition 4.10 | Semantic Domain                   | `VMap`                                                             | [src/Framework/VariantMap.agda](src/Framework/VariantMap.agda)                                       | In contrast to a variant map, the semantic domain is the type of variant maps instead of its elements.                                                             |
| Definition 4.11 | configuration language 𝐶          | `𝕂`                                                                | [src/Framework/Definitions.agda](src/Framework/Definitions.agda)                                     |                                                                                                                                                                    | -- TODO Use C instead of K if constructors are removed completely
| Definition 4.12 | variability language 𝐿            | `𝔼`                                                                | [src/Framework/Definitions.agda](src/Framework/Definitions.agda)                                     |                                                                                                                                                                    |
| Definition 4.13 | ⟦.⟧                               | `𝔼-Semantics`                                                      | [src/Framework/VariabilityLanguage.lagda.md](src/Framework/VariabilityLanguage.lagda.md)             |                                                                                                                                                                    |
|                 |                                   | `VariabilityLanguage`                                              | [src/Framework/VariabilityLanguage.lagda.md](src/Framework/VariabilityLanguage.lagda.md)             | VariabilityLanguage is a bundle of 𝔼, 𝕂 and 𝔼-Semantics.                                                                                                           |
| Definition 4.15 | Complete(𝐿)                       | `Complete`                                                         | [src/Framework/Properties/Completeness.lagda.md](src/Framework/Properties/Completeness.lagda.md)     |                                                                                                                                                                    |
| Definition 4.16 | Sound(𝐿)                          | `Sound`                                                            | [src/Framework/Properties/Soundness.lagda.md](src/Framework/Properties/Soundness.lagda.md)           |                                                                                                                                                                    |
| Definition 4.17 | ⪰                                 | `_≽_`                                                              | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≡                                 | `_≋_`                                                              | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≻                                 | `_≻_`                                                              | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Corollary 4.18  | ⪰ is a partial order              | `≽-IsPartialOrder`                                                 | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
|                 | ≡ is an equivalence relation      | `≋-IsEquivalence`                                                  | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Definition 4.19 | 𝑀 ⇾ 𝐿                             |                                                                    | [                                                                                                    | We](                                                                                                                                                               | We) only model correct compilers.                                                                          |
| Definition 4.20 | 𝑀 ⇾ 𝐿 correct                     | `LanguageCompiler`                                                 | [src/Framework/Compiler.agda](src/Framework/Compiler.agda)                                           |                                                                                                                                                                    |
| Theorem 4.21    | 𝑀 ⇾ 𝐿 ⇒ 𝐿 ⪰ 𝑀                     | `expressiveness-from-compiler`                                     | [src/Framework/Relation/Expressiveness.lagda.md](src/Framework/Relation/Expressiveness.lagda.md)     |                                                                                                                                                                    |
| Theorem 4.22    | Complete(M) ∧ L ≽ M ⇒ Complete(L) | `completeness-by-expressiveness`                                   | [src/Framework/Proof/Transitive.lagda.md](src/Framework/Proof/Transitive.lagda.md)                   |                                                                                                                                                                    |
| Theorem 4.23    | Sound(L) ∧ L ≽ M ⇒ Sound(M)       | `soundness-by-expressiveness`                                      | [src/Framework/Proof/Transitive.lagda.md](src/Framework/Proof/Transitive.lagda.md)                   |                                                                                                                                                                    |
| Theorem 4.24    | Complete(L) ∧ Sound(M) ⇒ L ≽ M    | `expressiveness-by-completeness-and-soundness`                     | [src/Framework/Proof/Transitive.lagda.md](src/Framework/Proof/Transitive.lagda.md)                   |                                                                                                                                                                    |
| Figure 3        |                                   |                                                                    | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         | This file mostly reexports expressiveness results and applies transitivity and the above theorems. It serves as a nice entry point to explore most of our results. |
| Theorem 5.1     | 𝑛-CC                              | `NCC`                                                              | [src/Lang/NCC.lagda.md](src/Lang/NCC.lagda.md)                                                       |                                                                                                                                                                    |
|                 | 𝑛-CC ⪰ CCC                        | `NCC≽CCC`                                                          | [src/Translation/Lang/CCC-to-NCC.agda](src/Translation/Lang/CCC-to-NCC.agda)                         |                                                                                                                                                                    |
|                 | clamp                             | `Exact.translate`                                                  | [src/Translation/Lang/CCC-to-NCC.agda](src/Translation/Lang/CCC-to-NCC.agda)                         |                                                                                                                                                                    | -- TODO this is not actually a compiler
|                 | shrink₂                           | `shrinkTo2Compiler`                                                | [src/Translation/Lang/NCC/ShrinkTo2.agda](src/Translation/Lang/NCC/ShrinkTo2.agda)                   |                                                                                                                                                                    |
|                 | grow                              | `growCompiler`                                                     | [src/Translation/Lang/NCC/Grow.agda](src/Translation/Lang/NCC/Grow.agda)                             |                                                                                                                                                                    |
| Theorem 5.3     | ADT ≽ 2CC                         | `ADT≽2CC`                                                          | [src/Translation/Lang/2CC-to-ADT.agda](src/Translation/Lang/2CC-to-ADT.agda)                         |                                                                                                                                                                    |
| Corollary 5.5   | CCC ≡ 2CC ≡ ADT ≡ 𝑛-CC            | `CCC≋NCC`, `NCC≋2CC`, and `2CC≋ADT`                                | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.6     | Complete(CaO)                     | `VariantList-is-Complete`                                          | [src/Lang/VariantList.lagda.md](src/Lang/VariantList.lagda.md)                                       |                                                                                                                                                                    |
| Theorem 5.7     | Sound(CaO)                        | `VariantList-is-Sound`                                             | [src/Lang/VariantList.lagda.md](src/Lang/VariantList.lagda.md)                                       |                                                                                                                                                                    |
| Theorem 5.8     | CaO ≽ ADT                         | `VariantList≽ADT`                                                  | [src/Translation/Lang/ADT-to-VariantList.agda](src/Translation/Lang/ADT-to-VariantList.agda)         |                                                                                                                                                                    |
| Theorem 5.10    | CCC ≽ CaO                         | `CCC≽VariantList`                                                  | [src/Translation/Lang/VariantList-to-CCC.lagda.md](src/Translation/Lang/VariantList-to-CCC.lagda.md) |                                                                                                                                                                    |
| Corollary 5.11  | CCC is complete and sound         | `CCC-is-complete`, `CCC-is-sound`                                  | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | 2CC is complete and sound         | `2CC-is-complete`, `2CC-is-sound`                                  | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | ADT is complete and sound         | `ADT-is-complete`, `ADT-is-sound`                                  | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | 𝑛-CC is complete and sound        | `NCC-is-complete`, `NCC-is-sound`                                  | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.12    | 2CC ≽ OC                          | `2CC≽OC`                                                           | [src/Translation/Lang/OC-to-2CC.lagda.md](src/Translation/Lang/OC-to-2CC.lagda.md)                   |                                                                                                                                                                    |
| Corollary 5.13  | Sound(OC)                         | `OC-is-sound`                                                      | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.14    | ¬Complete(OC)                     | `OC-is-incomplete`                                                 | [src/Lang/OC.lagda.md](src/Lang/OC.lagda.md)                                                         |                                                                                                                                                                    |
| Theorem 5.15    | 2CC ≻ OC                          | `2CC≻WFOC`                                                         | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
| Theorem 5.16    | ¬Complete(FST)                    | `FST-is-incomplete`                                                | [src/Lang/FST.agda](src/Lang/FST.agda)                                                               |                                                                                                                                                                    |
| Theorem 5.17    | OC ⋡ FST                          | `WFOCL⋡FSTL`                                                       | [src/Translation/Lang/FST-to-OC.lagda.md](src/Translation/Lang/FST-to-OC.lagda.md)                   |                                                                                                                                                                    | -- TODO remove L suffix
| Theorem 5.18    | FST ⋡ OC                          | `FSTL⋡WFOCL`                                                       | [src/Translation/Lang/OC-to-FST.agda](src/Translation/Lang/OC-to-FST.agda)                           |                                                                                                                                                                    | -- TODO remove L suffix, Why are both F's the same
| Corollary 5.19  | FST ⋡ 2CC                         | `FST⋡2CC`                                                          | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    | -- TODO Why are both F's the same
| Theorem 5.20    | Sound(FST)                        | `FST-is-sound`                                                     | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |
|                 | 2CC ≽ FST                         | `2CC≽FST`                                                          | [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md)                         |                                                                                                                                                                    |

> Note to the OOPSLA Artifact Reviewers:
> During formalization, we noticed that the proof of VariantList ≽ FST is easier than Sound(FST) and 2CC ≽ FST.
> Hence, we proof VariantList ≽ FST, conclude 2CC ≽ FST using transitivity and follow Sound(FST) from 2CC ≽ FST.
> We intend to adapt the proof in the paper to the formalized proof.


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

Of course, there are two exceptions to this.

##### Exception 1

For the [tutorials](src/Tutorial) (see above), we deliberately use many holes.
These holes are intended to be exercises for someone who is working through the tutorial.
We also use a terminating macro here to avoid sized types to keep the tutorial simple.
The place where we use the macro is proven to terminate throughout the rest
of the library multiple times, by using sized types.

##### Exception 2

For a non-crucial part of our framework, we included four postulates, which assume that two primitive operations from the standard library are invertible:

- converting `String`s to lists of characters and vice versa
- converting characters to natural numbers and vice versa.

These postulates can be found in [src/Util/String.agda](src/Util/String.agda).
We believe these postulates to be reasonable because strings are commonly _defined_ as lists of characters, and because characters are usually encoded as natural numbers in text encodings (e.g., UTF-8).
We use these axioms as an example, to prove that we can simplify annotations `String × ℕ` to just `String`, by turning a pair `s , n` into a String representation `s ++ "." ++ show n`.
This simplification only exists to beautify theorems (so they do not have to mention the pair) and align them more closely to our paper but our results would remain the same without that simplification.
In fact, these postulates are an open issue [#6119](https://github.com/agda/agda/issues/6119) in the Agda implementation.

### Limitations

- The library currently only supports abstract syntax for all languages. There are no parsers, so it is not yet possible to read in files or strings of concrete syntax.

## Troubleshooting

If you see an error similar to this one
```shell
.../src/MAlonzo/Code/Data/IndexedSet.hs:1705:3: error:
    Not in scope:
      type constructor or class ‘MAlonzo.Code.Agda.Primitive.T_Level_14’
    Perhaps you meant ‘MAlonzo.Code.Agda.Primitive.T_Level_18’ (imported from MAlonzo.Code.Agda.Primitive)
    Module ‘MAlonzo.Code.Agda.Primitive’ does not export ‘T_Level_14’.
     |
1705 |   MAlonzo.Code.Agda.Primitive.T_Level_14 ->
     |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
there might be corrupt build files. Simply run `make clean`.

[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3
[ghcup]: https://www.haskell.org/ghcup/
[plfa]: https://plfa.github.io/GettingStarted/
