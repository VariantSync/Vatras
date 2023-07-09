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

open import Framework.Definitions
open import Framework.Relation.Configuration using (≣ᶜ-setoid)

import Data.IndexedSet
private module ISet A = Data.IndexedSet (VariantSetoid ∞ A)
open import Util.Finity using (FiniteAndNonEmpty)
```

## Definitions

```agda
Sound : VariabilityLanguage → Set₁
Sound L = ∀ {A}
  → (e : Expression A L)
    ------------------------------
  → ∃[ n ] (Σ[ vs ∈ VMap A n ]
      (let open ISet A using (_≅_)
           ⟦_⟧ = semantics L ∘ get
        in vs ≅ ⟦ e ⟧))

Unsound : VariabilityLanguage → Set₁
Unsound L = ¬ (Sound L)

FiniteSemantics : (L : VariabilityLanguage) → Set₁
FiniteSemantics L = ∀ {A} (e : Expression A L) → FiniteAndNonEmpty (≣ᶜ-setoid e)
```

