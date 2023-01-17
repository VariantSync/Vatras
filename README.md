
# On the Expressive Power of Variability Languages

## Setup

The only dependency of the project is the agda standard library. I do not know the version I am using though (as I don't know yet how to know that).
I am using Agda version 2.6.2.2 but newer version should be fine too and I guess also some older versions, I did not do any testing on that.
To setup Agda and the standard library, I followed the guide from the _Programming Language Foundations in Agda_ (PLFA) book. You can finde the instructions [here](https://plfa.github.io/GettingStarted/). If everything works (hehe) then it should not take too long to setup Agda and the standard library.

As an editor, I am using spacemacs with agda-mode. Setting emacs up for Agda is also explained in the PFLA setup instructions linked above.

## Project Structure

The semantic domain of all languages is defined in [src/SemanticDomain.agda](src/SemanticDomain.agda). Variability languages, configuration languages, semantics, as well as relations between languages and translations are formalized in [src/Translation/Translation.lagda.md](src/Translation/Translation.lagda.md) (I plan to later modularize this later into _definitions of language kinds_, _definitions of language relations_, and _definitions of translations and their properties_). All languages are planned to be formalized in the [src/Lang](src/Lang) subdirectory in a custom file each. So far, [core choice calculus](src/Lang/CCC.lagda.md), [binary choice calculus](src/Lang/BCC.lagda.md), [option calculus](src/Lang/OC.lagda.md), and [algebraic decision diagrams](src/Lang/ADD.lagda.md) are formalized. Translations and theorems on relations between two such concrete languages are defined in the [src/Translation](src/Translation) directory. The only finished translation so far is [from binary to core choice calculus](src/Translation/BCC-to-CCC.lagda.md). Completeness and incompleteness are formalized in [src/Lang/Properties/Completeness.lagda.md](src/Lang/Properties/Completeness.lagda.md).

## (A bit outdated) Roadmap

![](res/taxonomy.jpg)

###

- [/] Relations for languages and translations
- [ ] Completeness and Incompleteness Theorems

### Choice Calculus
- [x] implement n-ary choice calculus
  - [x] syntax
  - [x] semantics
    - [x] semantic equivalence
    - [x] variant-preserving equivalence
    - [/] prove some transformation rules
- [x] implement binary choice calculus
  - [x] syntax
  - [x] semantics
- [/] bnf transformation
  - [x] implementation
  - [/] proof of being variant-preserving
    - [x] Binary CC -> CC
    - [ ] CC -> Binary CC
- [/] I already wrote a bidirectional translation from choice calculus to choice calculus with local dimension declarations in Haskell [here](https://github.com/VariantSync/ProofsCC/blob/main/src/CC/CCL.hs). The idea is that when not having local dimension declarations, one can identify the deepest spot in the choice calculus tree at which the declaration must be introduced. We could also add that to our map.

### Algebraic Decision Diagrams
- [/] implement algebaric decision diagrams (ADDs)
  - [x] syntax
  - [x] semantics
  - [x] prove that BDDs are specialized ADDs
  - [ ] prove that ADDs are equivalent to choice calculus by proving that a CC expression in binary normal form can be converted to ADD and vice versa. By transitivity `CC <-> Binary CC <-> ADD`, we get that any choice calculus expression can be transformed to ADD and vice versa.

- [ ] prove that choice calculus can encode any variation, by proving that we can build an ADD for any kind of variants. By transitivity we get that any ADD is also a CC expression and thus any set of variants can be encoded in CC.

### Option Calculus
on the search for nice brackets:
```
〔  U+3014  LEFT TORTOISE SHELL BRACKET (\( option 9 on page 2)
〕  U+3015  RIGHT TORTOISE SHELL BRACKET (\) option 9 on page 2)
```

- [ ] implement option calculus
  - [ ] syntax: Which dialect is the best? singleton options I guess!?
  - [ ] semantics
    - [ ] Decide on how to handle the empty variant induced by options at the root of an expression:
      - forbid?
      - make root option mandatory via semantics?
      - include empty variant explicitly?
  - [ ] are there any transformation rules?
- [ ] Show that option calculus is subsumed by choice calculus (except for the empty variant? s.a.)
  - [ ] implement conversion
  - [ ] proof of variant-preservingness
- [ ] Show that choice calculus is not subsumed by option calculus.

### Variation Trees
- [ ] implement variation trees
  - [ ] syntax
  - [ ] semantics
- [ ] prove that option calculus is subsumed by variation trees
- [ ] prove that choice calculus is subsumed by variation trees
- [ ] prove that there is nothing more in variation trees rather than option calculus and choice calculus (follows actually from syntax): This is essentially a proof that "option calculus + else = choice calculus".

### Artefact Trees
same as option calculus but with inline annotations?

### Variability-Aware ASTs
same as variation trees but with inline annotations?

### Literature Search on Further Formalisms

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

### On Variant Quantification (What is a Feature Mapping?)
- [ ] Generalization of Dimensions
- [ ] Generalization of Options
- Options and Binary Dimensions and thus feature mappings are expressions whose semantics is a predicate. For n-ary (core) choice calculus, such expression have semantics which is and indexing function (`Dim -> Nat`).
