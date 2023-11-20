```agda
{-# OPTIONS --sized-types #-}

module Framework.Relation.Configuration where

open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Function using (Congruent)
open import Level using (0ℓ)

open import Framework.Definitions
```

## Equivalence of Configurations

Two configurations are equivalent for an expression when they produce the same variants for all expressions.
```agda
_∋_⊢_≣ᶜ_ : ∀ {V S A}
  → (L : VariabilityLanguage V S)
  → Expression L A
  → (c₁ c₂ : S)
  → Set
(syn _ with-sem ⟦_⟧) ∋ e ⊢ c₁ ≣ᶜ c₂ = ⟦ e ⟧ c₁ ≡ ⟦ e ⟧ c₂
infix 5 _∋_⊢_≣ᶜ_

≣ᶜ-IsEquivalence : ∀ {V S A}
  → (L : VariabilityLanguage V S)
  → (e : Expression L A)
  → IsEquivalence (L ∋ e ⊢_≣ᶜ_)
≣ᶜ-IsEquivalence _ _ = record
  { refl  = Eq.refl
  ; sym   = Eq.sym
  ; trans = Eq.trans
  }

≣ᶜ-congruent : ∀ {V S A}
  → (L : VariabilityLanguage V S)
  → (e : Expression L A)
  → Congruent (L ∋ e ⊢_≣ᶜ_) _≡_ (Semantics L e)
≣ᶜ-congruent _ _ e⊢x≣ᶜy = e⊢x≣ᶜy

≣ᶜ-setoid : ∀ {V S A}
  → (L : VariabilityLanguage V S)
  → Expression L A
  → Setoid 0ℓ 0ℓ
≣ᶜ-setoid {_} {S} L e = record
  { Carrier       = S
  ; _≈_           = L ∋ e ⊢_≣ᶜ_
  ; isEquivalence = ≣ᶜ-IsEquivalence L e
  }
```
