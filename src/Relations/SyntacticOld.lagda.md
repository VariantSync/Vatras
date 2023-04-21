```agda
{-# OPTIONS --sized-types #-}

module Relations.SyntacticOld where
```

# Syntactic Relations of Variability Languages

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≗_)
open import Size using (Size)
open import Axioms.Extensionality using (_embeds-via_)
open import Definitions
```

So far, we covered relations between languages on a semantic level: Can we translate languages such that the translation describes the same set of variants as the original expression.
Some languages though exhibit stronger similarities, even up to syntactic equality.
For example, all terms in binary choice calculus _are_ also terms in core choice calculus.
This subset relation is not immediate in our formalization thought because both languages are modelled as their own datatypes and thus, syntactically equal terms are still instances of two different datatypes.

So how can we say that an expression `e` in a language `L` _is_ also an expression in another language `L'` (i.e., `e ∈ L` and `e ∈ L'`)?
To immediately obtain such a property, we would have to show that `e` is an instance of both types, which is impossible in Agda. (Todo: How is this property of a type system called?) What we can do however is matching constructors: When "translating" `e ∈ L` to `e' ∈ L'`, all we do is matching one constructor the at least one other constructor. If such a matching is injective, then we have shown that `e` is indeed an expression in `L'` up to some rewriting in terms of one or more constructors. We can then further constrain such a mapping to map each constructor to exactly one other constructor.

So what we want to say is: For every expression `e ∈ L₁`, having some constructor `C₁` at the top, there exists (exactly one / a) constructor `C₂` in `L₂` such that swapping the constructor from `C₁` to `C₂` in `e` yields a semantically equivalent expression `e₂ ∈ L₂`.

How can we formalized this in Agda though? One idea is to again treat constructors as their own types. A constructor for a variability language `L` is a function that takes some parameter `P` to produce an instance of that type.
```agda
VarLangConstructor : VarLang → Set₁
VarLangConstructor L = ∀ {i : Size} {A : Domain} {P : Set} → P → L i A
```
The set of constructors described by `VarLangConstructor L` for a language `L` is larger though than the actual set of `L`'s constructors as any function producing an `L`-expression would be a `VarLangConstructor L`. The constructors we seek are the "atomic" ones. Any `c : VarLangConstructor L` either is such an atomic constructor or composes an expression by applying atomic constructors one or more times. How can we identify the atomic constructors? This sounds like a job for category theory where we want to find some terminal/initial object.

TODO: More thinking. Can we properly express this in Agda? We could also comare constructors by looking at the translations outside of Agda.

### Weak Syntactic Equivalence

One observation is that, iff any term `e ∈ L₁` is also a term in `L₂`, then we it can be translated to L₂ and back to L₁ yielding the same term `e`.
Formalizing this constraint, would not guarantee that a translated term `e₂` is really syntactically equivalent to the original term `e₁` but it would depict that `e₂` contains enough information to recover `e₁` uniquely (but `e₂` might contain more information). This is a one-way isomorphism, also know as an embedding:
```agda
record LanguageEmbedding (L₁ L₂ : VarLang) : Set₁ where
  field
    to   : ∀ {i : Size} {D : Domain} → L₁ i D → L₂ i D
    from : ∀ {i : Size} {D : Domain} → L₂ i D → L₁ i D
    from∘to : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₁ i D} {L₂ i D} to from
open LanguageEmbedding public

record LanguageIsomorphism (L₁ L₂ : VarLang) : Set₁ where
  field
    to   : ∀ {i : Size} {D : Domain} → L₁ i D → L₂ i D
    from : ∀ {i : Size} {D : Domain} → L₂ i D → L₁ i D
    from∘to : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₁ i D} {L₂ i D} to from
    to∘from : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₂ i D} {L₁ i D} from to
open LanguageIsomorphism public

embedding→isomorphism : ∀ {L₁ L₂ : VarLang}
  → (1→2 : LanguageEmbedding L₁ L₂)
  → (2→1 : LanguageEmbedding L₂ L₁)
  → (∀ {i : Size} {D : Domain} → from 1→2 {i} {D} ≗   to 2→1 {i} {D})
  → (∀ {i : Size} {D : Domain} →   to 2→1 {i} {D} ≗ from 1→2 {i} {D})
    -------------------------
  → LanguageIsomorphism L₁ L₂
embedding→isomorphism 1→2 2→1 f≡t t≡f = record
  { to = to 1→2
  ; from = from 1→2
  ; from∘to = from∘to 1→2
  ; to∘from = λ e₂ → ({!!})
  }
```
Additionally, we enforce the size to be constant as the expression should not change anyway. A problem might be if the size constraint has different meanings in both langauges (e.g., depth vs. breadth). So we might want to weaken this in the future.

