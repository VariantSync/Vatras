```agda
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence; Setoid)
module Framework.Function.Relation.Index
  (O : Set → Setoid 0ℓ 0ℓ)
  where

open import Function using (_∘_; Congruent)
open import Framework.FunctionLanguage as FL
open FL.FunctionLanguage
```

## Equivalence of Indices

Two indices are equivalent for an expression when they produce the same output for all expressions.
```agda
module _ {A : Set} where
  open Setoid (O A)
  𝕃 = FunctionLanguage (Setoid.Carrier ∘ O)

  _∋_⊢_≣ⁱ_ :
    ∀ (L : 𝕃)
    → Expression L A
    → (c₁ c₂ : Input L)
    → Set
  ⟪ _ , _ , ⟦_⟧ ⟫ ∋ e ⊢ c₁ ≣ⁱ c₂ = ⟦ e ⟧ c₁ ≈ ⟦ e ⟧ c₂
  infix 5 _∋_⊢_≣ⁱ_

  ≣ⁱ-IsEquivalence :
    ∀ (L : 𝕃)
    → (e : Expression L A)
    → IsEquivalence (L ∋ e ⊢_≣ⁱ_)
  ≣ⁱ-IsEquivalence _ _ = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  ≣ⁱ-congruent :
    ∀ (L : 𝕃)
    → (e : Expression L A)
    → Congruent (L ∋ e ⊢_≣ⁱ_) _≈_ (Semantics L e)
  ≣ⁱ-congruent _ _ e⊢x≣ⁱy = e⊢x≣ⁱy

  ≣ⁱ-setoid :
    ∀ (L : 𝕃)
    → (e : Expression L A)
    → Setoid 0ℓ 0ℓ
  ≣ⁱ-setoid L e = record
    { Carrier       = Input L
    ; _≈_           = L ∋ e ⊢_≣ⁱ_
    ; isEquivalence = ≣ⁱ-IsEquivalence L e
    }
```
