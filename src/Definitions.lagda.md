```agda
{-# OPTIONS --sized-types #-}

module Definitions where
```

# Definitions of Central Abstractions for Variability Languages

```agda
open import Data.List using (List)
open import Size using (Size; Size<_)
open import SemanticDomain using (Variant)
```

## Languages

We model variability languages as embedded domain specific languages. That is, each variability language is described by a type which in turn is described by the kind `VarLang`. (`Set` denotes the set of all types and `Set₁` denotes the set of all kinds, i.e., the set of all sets of types).
Each language is parameterized in its domain (called _object language_ in choice calculus), such as text, source code, files, whatever.
We model domains, also as types, such as `String`, `ℕ`, or some AST of a programming language.
Each variability language `VarLang` is also parameterized in a size which is irrelevant for studying variation but we need it to ensure that our proofs terminate.
```agda
Domain : Set₁ -- Object Language
Domain = Set

VarLang : Set₁
VarLang = Size → Domain → Set
```

We also model configurations as types but they do not have parameters.
```agda
ConfLang : Set₁
ConfLang = Set
```

## Semantics

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → ConfLang → Set₁
Semantics L C = ∀ {i : Size} {A : Domain} → L i A → C → Variant A
```

## Helper Functions and Theorems

Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
```agda
Artifactˡ : VarLang → Set₁
Artifactˡ L = ∀ {i : Size} {j : Size< i} {A : Domain} → A → List (L j A) → L i A
```

Sometimes, it is convenient to invert the order of arguments for variability languages. So instead of speaking of a language `L i A` of size `i` over a domain `A`, we sometimes would like two write `L A i`.
When writing `L A i` we can observer that `L A` is a `Bounded` type which means it is a data type parameterized in only a size:
```agda
open import Util.SizeJuggle

flip-VarLang : VarLang → Domain → Bounded
flip-VarLang L A i = L i A
```

More helpers:
```agda
open import Data.List.NonEmpty using (List⁺)
open import Size using (↑_)
open import Util.Existence using (∃-Size; _,_)

{-
Creates an Artifact from a list of expressions of a certain size.
The size of the resulting expression is larger by 1.
-}
sequence-sized-artifact : ∀ {A : Domain}
  → {L : VarLang}
  → Weaken (flip-VarLang L A)
  → Artifactˡ L
  → A
  → List⁺ (∃-Size[ i ] (L i A))
    ---------------------------
  → ∃-Size[ i ] (L i A)
sequence-sized-artifact {A} {L} w Artifact a cs =
  let max , es = unify-sizes⁺ w cs
   in
      ↑ max ,
      Artifact {↑ max}
               {i<↑i max}
               {A}
               a
               (i<↑i-list (flip-VarLang L A) max es)
```
