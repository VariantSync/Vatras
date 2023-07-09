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

Two configurations are equivalent for an expressionwhen they produce the same variants for all expressions.
```agda
_⊢_≣ᶜ_ : ∀ {A : 𝔸} {L : VariabilityLanguage}
  → Expression A L
  → (c₁ c₂ : configuration L)
  → Set
_⊢_≣ᶜ_ {L = L} e c₁ c₂ = ⟦e⟧ c₁ ≡ ⟦e⟧ c₂
  where ⟦e⟧ = semantics L {size e} (get e)
infix 5 _⊢_≣ᶜ_

≣ᶜ-IsEquivalence : ∀ {A L} → (e : Expression A L) → IsEquivalence ( e ⊢_≣ᶜ_)
≣ᶜ-IsEquivalence _ = record
  { refl  = Eq.refl
  ; sym   = Eq.sym
  ; trans = Eq.trans
  }

≣ᶜ-congruent : ∀ {A L} → (e : Expression A L) → Congruent (e ⊢_≣ᶜ_) _≡_ (semantics L (get e))
≣ᶜ-congruent _ e⊢x≣ᶜy = e⊢x≣ᶜy

≣ᶜ-setoid : ∀ {A} {L : VariabilityLanguage}
  → Expression A L
  → Setoid 0ℓ 0ℓ
≣ᶜ-setoid {A} {L} e = record
  { Carrier       = configuration L
  ; _≈_           = e ⊢_≣ᶜ_
  ; isEquivalence = ≣ᶜ-IsEquivalence e
  }
```
