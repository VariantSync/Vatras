
# On the Expressive Power of Variability Languages

## Setup

The only dependency of the project is the agda standard library. I do not know the version I am using though (as I don't know yet how to know that).
I am using Agda version 2.6.2.2 but newer version should be fine too and I guess also some older versions, I did not do any testing on that.
To setup Agda and the standard library, I followed the guide from the _Programming Language Foundations in Agda_ (PLFA) book. You can finde the instructions [here](https://plfa.github.io/GettingStarted/). If everything works (hehe) then it should not take too long to setup Agda and the standard library.

As an editor, I am using spacemacs with agda-mode. Setting emacs up for Agda is also explained in the PFLA setup instructions linked above.

## Project Structure

Variants are defined in [src/SemanticDomain.agda](src/SemanticDomain.agda).
Core definitions are in [src/Definitions.lagda.md](/src/Definitions.lagda.md).
Languages are defined in [src/Lang](/src/Lang).
Language properties including completeness are defined in [src/Lang/Properties](src/Lang/Properties).
Translations are formalized in [src/Translation/Translation.lagda.md](src/Translation/Translation.lagda.md).
Translations between specific languages are defined in the [src/Translation](src/Translation) directory.
A comprehensive list of the progress on language translations and relations can be found the [src/Translation/LanguageMap.lagda.md](src/Translation/LanguageMap.lagda.md).

We also have a main function which runs experiments and tests.

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
- [ ] Lists of Variants (VList)?

For some of those language, showing the existence of some transforation rules might be handy. We did this for some few rules of CCC and BCC so far.

### Language Properties

- [x] Define Completeness
- [x] Define Incompleteness

- [ ] Completeness of ADD
- [ ] Completeness of CCC (begun; might be smarter to conclude from completeness of ADDs)
- [x] Incompleteness of OC
- [ ] Completeness of BCC
- [ ] Completeness of VT

### Language Relations

Comparing expression within a single language:

- [x] syntactic equivalence (defined in Agda STL)
- [x] variant subset
- [x] variant preserving equivalence
- [x] semantic equivalence

Comparing expression from two different languages:

- [x] variant subset
- [x] variant preserving equivalence
- [x] semantic equivalence

Comparing two languages

- [x] expressiveness
- [x] variant equivalence

### Translations

#### General Definitions

- [x] Translation
- [x] variant-preserving translations
- [x] semantics-preserving translations: Defined but is it useful?
- [x] conclude that a language is as expressive as another from a variant-preserving translation

#### Across Languages

planed proofs are:

- [/] CCC to BCC (begun; stuck in state monad)
- [x] BCC to CCC

- [ ] BCC to ADD
- [ ] ADD to BCC

- [x] OC to BCC
- [/] BCC cannot be encoded in OC

- [ ] OC to VT
- [ ] VT cannot be encoded in OC

- [ ] BCC to VT
- [ ] VT to BCC

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
