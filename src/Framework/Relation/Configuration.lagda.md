# Definitions for Relating Configurations.

```agda
open import Framework.Definitions using (𝕍; 𝔸)
module Framework.Relation.Configuration (V : 𝕍) where

open import Level using (0ℓ; suc)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; sym; trans)
open import Function using (_∘_; Congruent)
open import Framework.VariabilityLanguage
open import Data.EqIndexedSet
```

This module defines semantic equivalence of configurations.

Two configurations c₁ c₂ are considered equivalent for an
expression e ∈ L (written "L ∋ e ⊢ c₁ ≣ⁱ c₂") if the configurations
configure e to the same variant.
Our definition reuses the definition of index equivalence of
indexed sets `_⊢_≡ⁱ_`.
```agda
_∋_⊢_≣ⁱ_ : ∀ {A : 𝔸}
  → (L : VariabilityLanguage V)
  → Expression L A
  → (c₁ c₂ : Config L)
  → Set₁
⟪ _ , _ , ⟦_⟧ ⟫ ∋ e ⊢ c₁ ≣ⁱ c₂ = ⟦ e ⟧ ⊢ c₁ ≡ⁱ c₂
infix 5 _∋_⊢_≣ⁱ_
```

We now prove a range of useful properties
of configuration equivalence.
These properties are basically just aliases
for the respective proofs on indexed sets.

```agda
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
