
# On the Expressive Power of Variability Languages

## Setup

The only dependency of the project is the agda standard library. I do not know the version I am using though (as I don't know yet how to know that).
I am using Agda version 2.6.2.2 but newer version should be fine too and I guess also some older versions, I did not do any testing on that.
To setup Agda and the standard library, I followed the guide from the _Programming Language Foundations in Agda_ (PLFA) book. You can finde the instructions [here](https://plfa.github.io/GettingStarted/). If everything works (hehe) then it should not take too long to setup Agda and the standard library.

As an editor, I am using spacemacs with agda-mode. Setting emacs up for Agda is also explained in the PFLA setup instructions linked above.

## Project Structure

The semantic domain of all languages is defined in [src/SemanticDomain.agda](src/SemanticDomain.agda). Variability languages, configuration languages, semantics, as well as relations between languages and translations are formalized in [src/Translation/Translation.lagda.md](src/Translation/Translation.lagda.md) (I plan to later modularize this later into _definitions of language kinds_, _definitions of language relations_, and _definitions of translations and their properties_). All languages are planned to be formalized in the [src/Lang](src/Lang) subdirectory in a custom file each. So far, [core choice calculus](src/Lang/CCC.lagda.md), [binary choice calculus](src/Lang/BCC.lagda.md), [option calculus](src/Lang/OC.lagda.md), and [algebraic decision diagrams](src/Lang/ADD.lagda.md) are formalized. Translations and theorems on relations between two such concrete languages are defined in the [src/Translation](src/Translation) directory. The only finished translation so far is [from binary to core choice calculus](src/Translation/BCC-to-CCC.lagda.md). Completeness and incompleteness are formalized in [src/Lang/Properties/Completeness.lagda.md](src/Lang/Properties/Completeness.lagda.md).

## Roadmap

![](res/taxonomy.jpg)

## Implementation Progress

### Language Formalizations

- [x] Core Choice Calculus (CCC)
- [x] Binary Choice Calculus (BCC)
- [x] Algebraic Decision Diagrams (ADD)
- [x] Binary Decision Diagrams (BDD)
- [x] Option Calculus (OC)
- [ ] Variation Trees (VT)

For some of those language, showing the existence of some transforation rules might be handy. We did this for some few rules of CCC and BCC so far.

Languages we might also want to include are

- [ ] Formula Choice Calculus
- [ ] Artifact Trees (i.e., Option Calculus with Formulas + formulas stored within artifact nodes)
- [ ] Variability-Aware ASTs
- [ ] ...?

## Language Properties

### In general

- [x] Completeness
- [x] Incompleteness

### In concrete

- [ ] Completeness of ADD
- [ ] Completeness of CCC (begun; might be smarter to conclude from completeness of ADDs)
- [x] Incompleteness of OC
- [ ] Completeness of BCC
- [ ] Completeness of VT

We can derive some completeness proofs by transitivity with translations.

## Language Relations

Comparing expression within a single language:

- [x] syntactic equivalence (defined in Agda STL)
- [x] variant subset
- [x] variant preserving equivalence
- [x] semantic equivalence

Comparing expression from two different languages:

- syntactic equivalence does not exist
- [x] variant subset
- [x] variant preserving equivalence
- [x] semantic equivalence

Comparing two languages

- [x] expressiveness
- [x] variant equivalence

## Translations

### General Definitions

- [x] Translation
- [x] variant-preserving translations
- [x] semantics-preserving translations: Defined but is it useful?
- [x] conclude that a language is as expressive as another from a variant-preserving translation

### Across Languages

planed proofs are:

- [ ] CCC to BCC (begun; stuck in state monad)
- [x] BCC to CCC

- [ ] BCC to ADD
- [ ] ADD to BCC

- [ ] OC to BCC
- [ ] BCC cannot be encoded in OC

- [ ] OC to VT
- [ ] VT cannot be encoded in OC

- [ ] BCC to VT
- [ ] VT to BCC

- [ ] BDD to ADD
- [ ] ADD cannot be encoded in BDD

## Annotation Languages

Do we want to also abstract on the annotation language (i.e., dimensions vs. formulas vs. literals vs. ... any expression that describes a predicate (or an indexing `X \to N` for CCC))? This might be a good future work. This would require to generalize all the languages to tak the annotation langauge as a type parameter, thus yielding a family of variation language for every current language. I'd love to do this in the future but I think that might be too much for this paper.

## Some other notes and thoughts

- Eric used the core choice calculus + local dimension declarations in his phd thesis. I wrote a bidirectional translation from choice calculus to choice calculus with local dimension declarations in Haskell [here](https://github.com/VariantSync/ProofsCC/blob/main/src/CC/CCL.hs). The idea is that when not having local dimension declarations, one can identify the deepest spot in the choice calculus tree at which the declaration must be introduced. We could also add that to our map.
- on the search for nice brackets for option calculus I found these in Agda
  ```
  〔  U+3014  LEFT TORTOISE SHELL BRACKET (\( option 9 on page 2)
  〕  U+3015  RIGHT TORTOISE SHELL BRACKET (\) option 9 on page 2)
  ```
- We somehow would like to prove that there is nothing more in variation trees than option calculus and choice calculus (follows actually from syntax): This is essentially a proof that "option calculus + else = choice calculus".

### Sharing
- [ ] Investigate sharing.
  - [ ] prove for which set of problems, OC is better?
  - [ ] In case, `option calculus + else = choice calculus`, we get `variation trees = choice calculus` but with better sharing!

## Future Work
### Evolution
- [ ] implement variation diffs
  - [ ] syntax as Variation Tree subset with meta-variation nodes
  - [ ] semantics
  - [ ] semantics for free from CC/VT. Prove that it is equivalent to the self-defined semantics (commuting square)
  - [ ] derivation
  - [ ] integration
