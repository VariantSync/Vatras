
# On the Expressive Power of Variability Languages

This is the supplementary Agda library for our paper _On the Expressive Power of Variability Languages_ submitted to 51st ACM SIGPLAN Symposium on Principles of Programming Languages (POPL 2024).

## Setup

We tested our setup on ubuntu (inside windows subsystem for linux (WSL 2)).

To compile the library and run its small demo, you need to have Agda and it's standard-library installed.
We recommend following the installation instructions from the [Programming Language Foundations in Agda](https://plfa.github.io/GettingStarted/) book.
It gives you step-by-step instructions for installing the GHC compiler (if you have not installed it already), Agda, and the standard library (together with the book's source code).

We tested our library with Agda 2.6.2.2 and Agda 2.6.3.
We use standard library version installed manually at commit 625a5775 but also newer versions should work when following the instructions from the book.

To test whether you setup agda correctly, and to run this libraries demo, run make:
```shell
make
```
which will run the following commands to build the library and run it's demo:
```shell
agda --compile src/Main.agda
./src/Main
```

Building for the first time will take a while because Agda has to build the required dependencies from the standard library, too.
Running the demo will print some translations of core to binary choice calculus, and translations from option calculus to binary choice calculus.
When running the demo, make sure your terminal is in full-screen because the demo assumes to have at least 100 characters of horizontal space in the terminal for pretty-printing.

## Project Structure

The library is organized as follows:

- [src/Framework](src/Framework) contains the definitions of our formal framework, defined in Section 4 in our paper.
  You can find the core data types in [Definitions.lagda.md](src/Framework/Definitions.lagda.md).
  Soundness and completeness are defined in the [Properties](src/Framework/Properties) sub-directory.
  Definitions for expressiveness and other relations are in the [Relation](src/Framework/Relation) sub-directory.
  Theorems for proving completeness, soundness, and expressiveness based on their relationships (Section 4.5) are within the [Proof](src/Framework/Proof) sub-directory.
- [src/Lang](src/Lang) contains instantiations of particular variability languages.
- [src/Translation](src/Translation) contains translations between variability languages, such as the translation of option calculus to binary choice calculus in [OC-to-BCC.lagda.md](src/Translation/OC-to-BCC.lagda.md) (Section 5.3 in our paper).
- [src/Test](src/Test) contains definitions of unit tests for translations and some experiments that are run, when running the library.
