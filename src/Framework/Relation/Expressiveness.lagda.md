```agda
{-# OPTIONS --sized-types #-}

module Framework.Relation.Expressiveness where

open import Data.Product   using (_,_; Σ-syntax; _×_)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Framework.Definitions
open import Framework.Relation.Expression using (_≚_)

import Data.IndexedSet as ISet
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
```agda
{-|
Core expressiveness relation that constitutes a partial order of variability languages.
L₁ ≽ L₂ reads as L₁ is at least as expressive as L₂.
-}
_≽_ : VariabilityLanguage → VariabilityLanguage → Set₁ --\succeq
L₁ ≽ L₂ =
  ∀ {A : 𝔸} (e₂ : Expression A L₂) →
      (Σ[ e₁ ∈ Expression A L₁ ]
        (e₂ ≚ e₁))
  -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but first we have to generalize our multisets somehow to allow keys in the source set.

_⋡_ : VariabilityLanguage → VariabilityLanguage → Set₁ -- \nsucceq
L₁ ⋡ L₂ = ¬ (L₁ ≽ L₂)

_≻_ : VariabilityLanguage → VariabilityLanguage → Set₁ -- \succ
L₁ ≻ L₂ = L₁ ≽ L₂ × L₂ ⋡ L₁

_≋_ : VariabilityLanguage → VariabilityLanguage → Set₁ --\~~~
L₁ ≋ L₂ = (L₁ ≽ L₂) × (L₂ ≽ L₁)

-- Aliases for the above definitions that spell out their meaning:
_is-at-least-as-expressive-as_ = _≽_
_is-less-expressive-than_ = _⋡_
_is-more-expressive-than_ = _≻_
_is-equally-expressive-as_ = _≋_
```

Expressiveness forms a partial order:
```agda
≽-refl' : ∀ {L₁ L₂ : VariabilityLanguage}
  → L₁ ≡ L₂
    --------
  → L₁ ≽ L₂
≽-refl' {L₁} L₁≡L₂ e rewrite L₁≡L₂ = e , (λ i → i , refl) , (λ i → i , refl) -- TODO: Reuse other refl-proofs here

≽-refl : ∀ {L : VariabilityLanguage}
    ------
  → L ≽ L
≽-refl = ≽-refl' refl

≽-trans : ∀ {L₁ L₂ L₃ : VariabilityLanguage}
  → L₁ ≽ L₂
  → L₂ ≽ L₃
    --------
  → L₁ ≽ L₃
≽-trans L₂→L₁ L₃→L₂ {A} e₃ =
  let open ISet (VariantSetoid _ A)
      e₂ , e₃≚e₂ = L₃→L₂ e₃
      e₁ , e₂≚e₁ = L₂→L₁ e₂
   in e₁ , ≅-trans e₃≚e₂ e₂≚e₁ -- This proof is highly similar to ≅-trans itself. Maybe we could indeed reuse here.

≽-antisym : ∀ {L₁ L₂}
  → L₁ ≽ L₂
  → L₂ ≽ L₁
    --------
  → L₁ ≋ L₂
≽-antisym L₁≽L₂ L₂≽L₁ = L₁≽L₂ , L₂≽L₁
```

Variant-Equivalence is an equivalence relations:
```agda
≋-sym : ∀ {L₁ L₂ : VariabilityLanguage}
  → L₁ ≋ L₂
    ------------------------------
  → L₂ ≋ L₁
≋-sym (L₁≽L₂ , L₂≽L₁) = L₂≽L₁ , L₁≽L₂

≋-trans : ∀ {L₁ L₂ L₃}
  → L₁ ≋ L₂
  → L₂ ≋ L₃
    ------------------------------
  → L₁ ≋ L₃
≋-trans (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂) =
    ≽-trans L₁≽L₂ L₂≽L₃
  , ≽-trans L₃≽L₂ L₂≽L₁

≋-IsEquivalence : IsEquivalence _is-equally-expressive-as_
≋-IsEquivalence = record
  { refl  = ≽-refl , ≽-refl
  ; sym   = ≋-sym
  ; trans = ≋-trans
  }
```
