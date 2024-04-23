```agda
open import Framework.Definitions using (𝕍; 𝔸)
module Framework.Relation.Index where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; sym; trans)
open import Function using (_∘_; Congruent)
open import Framework.VariabilityLanguage
```

## Equivalence of Indices

Two indices are equivalent for an expression when they produce the same output for all expressions.
We can actually generalize this to index equivalence on indexed sets (TODO).
```agda
𝕃 = VariabilityLanguage

module _ {A : 𝔸} where
  _∋_⊢_≣ⁱ_ :
    ∀ (L : 𝕃)
    → Expression L A
    → (c₁ c₂ : Config L)
    → Set
  ⟪ _ , _ , ⟦_⟧ ⟫ ∋ e ⊢ c₁ ≣ⁱ c₂ = ⟦ e ⟧ c₁ ≡ ⟦ e ⟧ c₂
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
    → Congruent (L ∋ e ⊢_≣ⁱ_) _≡_ (Semantics L e)
  ≣ⁱ-congruent _ _ e⊢x≣ⁱy = e⊢x≣ⁱy

  ≣ⁱ-setoid :
    ∀ (L : 𝕃)
    → (e : Expression L A)
    → Setoid 0ℓ 0ℓ
  ≣ⁱ-setoid L e = record
    { Carrier       = Config L
    ; _≈_           = L ∋ e ⊢_≣ⁱ_
    ; isEquivalence = ≣ⁱ-IsEquivalence L e
    }
```
