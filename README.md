
# Roadmap of Option Calculus

## On the Structure of Variability

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

### Algebraic Decision Diagrams
- [/] implement algebaric decision diagrams (ADDs)
  - [x] syntax
  - [ ] semantics
  - [x] prove that BDDs are specialized ADDs
  - [ ] prove that ADDs are equivalent to choice calculus by proving that a cc expression in binary normal form can be converted to ADD and vice versa. By transitivity `CC <-> Binary CC <-> ADD`, we get that any choice calculus expression can be transformed to ADD and vice versa.

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
