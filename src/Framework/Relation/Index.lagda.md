# Definitions for Relating configurations.

```agda
open import Framework.Definitions using (𝕍; 𝔸)
module Framework.Relation.Index (V : 𝕍) where

open import Level using (0ℓ; suc)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; sym; trans)
open import Function using (_∘_; Congruent)
open import Framework.VariabilityLanguage
open import Data.EqIndexedSet
```

## Equivalence of Indices

Two indices are equivalent for an expression when they produce the same output for all expressions.
```agda
_∋_⊢_≣ⁱ_ : ∀ {A : 𝔸}
  → (L : VariabilityLanguage V)
  → Expression L A
  → (c₁ c₂ : Config L)
  → Set₁
⟪ _ , _ , ⟦_⟧ ⟫ ∋ e ⊢ c₁ ≣ⁱ c₂ = ⟦ e ⟧ ⊢ c₁ ≡ⁱ c₂
infix 5 _∋_⊢_≣ⁱ_

≣ⁱ-congruent : ∀ {A : 𝔸}
  → (L : VariabilityLanguage V)
  → (e : Expression L A)
  → Congruent (L ∋ e ⊢_≣ⁱ_) _≡_ (Semantics L e)
≣ⁱ-congruent L e = ≡ⁱ-congruent (Semantics L e)

≣ⁱ-IsEquivalence : ∀ {A : 𝔸}
  → (L : VariabilityLanguage V)
  → (e : Expression L A)
  → IsEquivalence (L ∋ e ⊢_≣ⁱ_)
≣ⁱ-IsEquivalence _ _ = ≡ⁱ-IsEquivalence

≣ⁱ-setoid : ∀ {A : 𝔸}
  → (L : VariabilityLanguage V)
  → (e : Expression L A)
  → Setoid 0ℓ (suc 0ℓ)
≣ⁱ-setoid L e = record
  { Carrier       = Config L
  ; _≈_           = L ∋ e ⊢_≣ⁱ_
  ; isEquivalence = ≡ⁱ-IsEquivalence
  }
```
