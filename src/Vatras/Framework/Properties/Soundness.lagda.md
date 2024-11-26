# Soundness and Unsoundness of Variability Languages

## Module

```agda
open import Vatras.Framework.Definitions using (𝕍)
module Vatras.Framework.Properties.Soundness (V : 𝕍) where
```

## Imports

```agda
open import Data.Product using (∃-syntax; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.VariantGenerator V
open import Vatras.Data.EqIndexedSet
```

## Definitions

A language is sound if every expression denotes an element in the semantic domain.
For variability languages, this means that for any expression `e` there must exist a variant generator `m` that is semantically equivalent.
```agda
Sound : VariabilityLanguage V → Set₁
Sound ⟪ E , _ , ⟦_⟧ ⟫ =
  ∀ {A} (e : E A)
    ----------------------------------
  → ∃[ n ] Σ[ m ∈ VariantGenerator A n ] m ≅ ⟦ e ⟧
```

We define unsoundness as the negation of soundness.
```agda
Unsound : VariabilityLanguage V → Set₁
Unsound L = ¬ (Sound L)
```
