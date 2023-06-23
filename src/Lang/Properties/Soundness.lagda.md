# The set of variants described by a language can be enumerated

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.Properties.Soundness where
```

## Imports

```agda
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; Σ-syntax)

open import Function using (Surjective)
open import Size using (∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Definitions
open import Relations.Semantic using (_⊢_≣ᶜ_)

import Data.Multiset
private module MSet A = Data.Multiset (VariantSetoid ∞ A)
```

## Definitions

```agda
Sound : VariabilityLanguage → Set₁
Sound L = ∀ {A}
  → (e : Expression A L)
    ------------------------------
  → ∃[ I ] (Σ[ vs ∈ VSet A I ]
      (let open MSet A using (_≅_)
           ⟦_⟧ = semantics L
        in vs ≅ ⟦ get e ⟧))

record FiniteSemantics (A : Domain) (L : VariabilityLanguage) : Set₁ where
  field
    {-|
    Computes a lower bound of the number of variants described by a given expression.
    The expression should thus describe at least the returned amount of variants - 1.
    -}
    # : Expression A L → ℕ

    {-|
    Identifies each configuration of a given expression by a natural number.
    This is the first step of proving that there exist only a finite amount of
    configurations, and thus variants described by the expression.
    -}
    pick : (e : Expression A L) → Fin (suc (# e)) → configuration L

    {-|
    Identification of configurations has to be surjective:
    Every configuration is indexed.
    While there might be infinitely many configurations, there must be a finite subset
    of configurations that describes all variants.
    This means that surjectivity actually means:
    For every configuration, there exists a configuration that is picked by pick and
    is semantically equivalent (w.r.t., e ⊢_≣ᶜ_).
    Thus, pick must be be surjective on the subset of unique configurations within a
    given expression e.
    -}
    pick-surjective : ∀ {e} → Surjective _≡_ (_⊢_≣ᶜ_ e) (pick e)
open FiniteSemantics public
```

