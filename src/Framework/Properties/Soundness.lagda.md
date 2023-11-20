# The set of variants described by a language can be enumerated

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Framework.Properties.Soundness where
```

## Imports

```agda
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; Σ-syntax)

open import Function using (_∘_)
open import Size using (∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Variant
open import Framework.Definitions
open import Framework.Relation.Configuration using (≣ᶜ-setoid)

import Data.IndexedSet
open import Util.Finity using (FiniteAndNonEmpty)
```

## Definitions

```agda
Sound : ∀ {V S} → VariabilityLanguage V S → Set₁
Sound {V} (syn Expr with-sem ⟦_⟧) = ∀ {A}
  → (e : Expr A)
    --------------------------------
  → ∃[ n ] (Σ[ vs ∈ VMap V A n ]
      let open IVSet V A using (_≅_)
        in vs ≅ ⟦ e ⟧)

Unsound : ∀ {V S} → VariabilityLanguage V S → Set₁
Unsound L = ¬ (Sound L)

FiniteSemantics : ∀ {V S} → (L : VariabilityLanguage V S) → Set₁
FiniteSemantics L = ∀ {A} (e : Expression L A) → FiniteAndNonEmpty (≣ᶜ-setoid L e)
```

