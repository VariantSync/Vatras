# The set of variants described by a language can be enumerated

## Module

```agda
open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
module Framework.Function.Properties.Soundness
  (O : Set → Setoid 0ℓ 0ℓ)
  (P : Set)
  (I : P → Set)
  where
```

## Imports

```agda
open import Data.Product using (∃-syntax; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Framework.FunctionLanguage
open import Framework.Function.Relation.Index using (≣ⁱ-setoid)
open import Function using (_∘_)
import Data.IndexedSet
```

## Definitions

```agda
Sound : FunctionLanguage (Setoid.Carrier ∘ O) → Set₁
Sound ⟪ Expr , _ , ⟦_⟧ ⟫ =
  ∀ {A} → let open Data.IndexedSet (O A) in
  ∀ (e : Expr A)
    --------------------------------
  → ∃[ p ] Σ[ m ∈ IndexedSet (I p) ] m ≅ ⟦ e ⟧

Unsound : FunctionLanguage (Setoid.Carrier ∘ O) → Set₁
Unsound L = ¬ (Sound L)
```
