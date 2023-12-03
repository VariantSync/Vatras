# The set of variants described by a language can be enumerated

## Module

```agda
open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
module Framework.Function.Properties.Soundness
  (O : Setoid 0ℓ 0ℓ)
  (I : Set)
  where
```

## Imports

```agda
open import Data.Product using (∃-syntax; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Framework.FunctionLanguage
open import Framework.Function.Relation.Index using (≣ⁱ-setoid)
open import Data.IndexedSet O using (IndexedSet; _≅_)
open Setoid O
```

## Definitions

```agda
Sound : FunctionLanguage Carrier → Set
Sound ⟪ Expr , _ , ⟦_⟧ ⟫ =
  ∀ (e : Expr)
    --------------------------------
  → Σ[ m ∈ IndexedSet I ] m ≅ ⟦ e ⟧

Unsound : FunctionLanguage Carrier → Set
Unsound L = ¬ (Sound L)
```
