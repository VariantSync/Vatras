```agda
{-# OPTIONS --sized-types #-}

module Framework.Relation.Expressiveness where

open import Data.Product   using (_,_; Σ-syntax; _×_)

open import Relation.Binary using (IsEquivalence; Reflexive; Sym; Trans; Antisym)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Variant
open import Framework.Definitions
open import Framework.Relation.Expression using (_,_⊢_≚_)

import Data.IndexedSet
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
```agda
{-|
Core expressiveness relation that constitutes a partial order of variability languages.
L₁ ≽ L₂ reads as L₁ is at least as expressive as L₂.
-}
_≽_ : ∀ {V S₁ S₂} → VariabilityLanguage V S₁ → VariabilityLanguage V S₂ → Set₁ --\succeq
L₁ ≽ L₂ =
  ∀ {A : 𝔸} (e₂ : Expression L₂ A) →
      (Σ[ e₁ ∈ Expression L₁ A ] L₂ , L₁ ⊢ e₂ ≚ e₁)
  -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but first we have to generalize our multisets somehow to allow keys in the source set.

_⋡_ : ∀ {V S₁ S₂} → VariabilityLanguage V S₁ → VariabilityLanguage V S₂ → Set₁ -- \nsucceq
L₁ ⋡ L₂ = ¬ (L₁ ≽ L₂)

_≻_ : ∀ {V S₁ S₂} → VariabilityLanguage V S₁ → VariabilityLanguage V S₂ → Set₁ -- \succ
L₁ ≻ L₂ = L₁ ≽ L₂ × L₂ ⋡ L₁

_≋_ : ∀ {V S₁ S₂} → VariabilityLanguage V S₁ → VariabilityLanguage V S₂ → Set₁ --\~~~
L₁ ≋ L₂ = (L₁ ≽ L₂) × (L₂ ≽ L₁)

-- Aliases for the above definitions that spell out their meaning:
_is-at-least-as-expressive-as_ = _≽_
_is-less-expressive-than_ = _⋡_
_is-more-expressive-than_ = _≻_
_is-equally-expressive-as_ = _≋_
```

Expressiveness forms a partial order:
```agda
≽-refl' : ∀ {V S}
  → (L₁ L₂ : VariabilityLanguage V S)
  → L₁ ≡ L₂
    --------
  → L₁ ≽ L₂
≽-refl' {V} _ _ L₁≡L₂ e rewrite L₁≡L₂ = e , ≅-refl
  where
    open IVSet V _ using (≅-refl)

≽-refl : ∀ {V S} → Reflexive (_≽_ {V} {S})
≽-refl {x = L} = ≽-refl' L L refl

≽-trans : ∀ {V S₁ S₂ S₃} → Trans (_≽_ {V} {S₁} {S₂}) (_≽_ {V} {S₂} {S₃}) (_≽_ {V} {S₁} {S₃})
≽-trans {V} L₂→L₁ L₃→L₂ {A} e₃ =
  let open IVSet V A
      e₂ , e₃≚e₂ = L₃→L₂ e₃
      e₁ , e₂≚e₁ = L₂→L₁ e₂
   in e₁ , ≅-trans e₃≚e₂ e₂≚e₁ -- This proof is highly similar to ≅-trans itself. Maybe we could indeed reuse it here on a "higher index order".

≽-antisym : ∀ {V S₁ S₂} → Antisym (_≽_ {V} {S₁} {S₂}) (_≽_ {V} {S₂} {S₁}) (_≋_ {V} {S₁} {S₂})
≽-antisym L₁≽L₂ L₂≽L₁ = L₁≽L₂ , L₂≽L₁
```

Variant-Equivalence is an equivalence relations:
```agda
≋-refl : ∀ {V S} → Reflexive (_≋_ {V} {S} {S})
≋-refl {x = L} = ≽-refl {x = L} , ≽-refl {x = L}

≋-sym : ∀ {V S₁ S₂} → Sym (_≋_ {V} {S₁} {S₂}) (_≋_ {V} {S₂} {S₁})
≋-sym (L₁≽L₂ , L₂≽L₁) = L₂≽L₁ , L₁≽L₂

≋-trans : ∀ {V S₁ S₂ S₃} → Trans (_≋_ {V} {S₁} {S₂}) (_≋_ {V} {S₂} {S₃}) (_≋_ {V} {S₁} {S₃})
≋-trans {i = L₁} {k = L₃}
        (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂)
        = ≽-trans {i = L₁} L₁≽L₂ L₂≽L₃ , ≽-trans {i = L₃} L₃≽L₂ L₂≽L₁

-- ≋-IsEquivalence : ∀ {V S₁ S₂} → IsEquivalence (_≋_ {V} {S₁} {S₂})
-- ≋-IsEquivalence = record
--   { refl  = ≋-refl
--   ; sym   = ≋-sym
--   ; trans = ≋-trans
--   }
```
