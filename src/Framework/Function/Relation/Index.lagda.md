```agda
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence; Setoid)
module Framework.Function.Relation.Index
  (O : Setoid 0ℓ 0ℓ)
  where

open import Function using (Congruent)
open import Framework.FunctionLanguage as FL
open FL.FunctionLanguage
open Setoid O
```

## Equivalence of Indices

Two indices are equivalent for an expression when they produce the same output for all expressions.
```agda
_∋_⊢_≣ⁱ_ :
  ∀ (L : FunctionLanguage Carrier)
  → Expression L
  → (c₁ c₂ : Input L)
  → Set
⟪ _ , _ , ⟦_⟧ ⟫ ∋ e ⊢ c₁ ≣ⁱ c₂ = ⟦ e ⟧ c₁ ≈ ⟦ e ⟧ c₂
infix 5 _∋_⊢_≣ⁱ_

≣ⁱ-IsEquivalence :
  ∀ (L : FunctionLanguage Carrier)
  → (e : Expression L)
  → IsEquivalence (L ∋ e ⊢_≣ⁱ_)
≣ⁱ-IsEquivalence _ _ = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

≣ⁱ-congruent :
  ∀ (L : FunctionLanguage Carrier)
  → (e : Expression L)
  → Congruent (L ∋ e ⊢_≣ⁱ_) _≈_ (Semantics L e)
≣ⁱ-congruent _ _ e⊢x≣ⁱy = e⊢x≣ⁱy

≣ⁱ-setoid :
  ∀ (L : FunctionLanguage Carrier)
  → (e : Expression L)
  → Setoid 0ℓ 0ℓ
≣ⁱ-setoid L e = record
  { Carrier       = Input L
  ; _≈_           = L ∋ e ⊢_≣ⁱ_
  ; isEquivalence = ≣ⁱ-IsEquivalence L e
  }
```
