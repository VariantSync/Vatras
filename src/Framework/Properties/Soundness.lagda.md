# The set of variants described by a language can be enumerated

## Module

```agda
open import Framework.Definitions using (𝕍)
module Framework.Properties.Soundness where
```

## Imports

```agda
open import Data.Product using (∃-syntax; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Framework.VariabilityLanguage
open import Framework.VariantMap
open import Data.EqIndexedSet
```

## Definitions

```agda
Sound : VariabilityLanguage → Set₁
Sound ⟪ E , _ , ⟦_⟧ ⟫ =
  ∀ {A} (e : E A)
    --------------------------------
  → ∃[ n ] Σ[ m ∈ VMap A n ] m ≅ ⟦ e ⟧

Unsound : VariabilityLanguage → Set₁
Unsound L = ¬ (Sound L)
```
