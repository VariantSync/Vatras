```agda
open import Framework.Definitions
module Framework.Relation.Expressiveness (V : 𝕍) where

open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans)
open import Function using (_∘_; Injective)

open import Framework.VariabilityLanguage
open import Framework.Variant V
open import Framework.Relation.Expression V
open import Framework.Relation.Function using (_⇒ₚ_)
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same function.
This means that there exists a translation from `L₂` to `L₁`, , thus `L₁` can model `L₂`:
```agda
{-|
Core expressiveness relation that constitutes a partial order of variability languages.
L₁ ≽ L₂ reads as L₁ is at least as expressive as L₂.
-}
_≽_ : ∀ (L₁ L₂ : VariabilityLanguage V) → Set₁ --\succeq
L₁ ≽ L₂ =
  ∀ {A : 𝔸} (e₂ : Expression L₂ A) →
      (Σ[ e₁ ∈ Expression L₁ A ] L₂ , L₁ ⊢ e₂ ≣ e₁)
  -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but first we have to generalize our multisets somehow to allow keys in the source set.

_⋡_ : ∀ (L₁ L₂ : VariabilityLanguage V) → Set₁ -- \nsucceq
L₁ ⋡ L₂ = ¬ (L₁ ≽ L₂)

_≻_ : ∀ (L₁ L₂ : VariabilityLanguage V) → Set₁ -- \succ
L₁ ≻ L₂ = L₁ ≽ L₂ × L₂ ⋡ L₁

_≋_ : ∀ (L₁ L₂ : VariabilityLanguage V) → Set₁ --\~~~
L₁ ≋ L₂ = (L₁ ≽ L₂) × (L₂ ≽ L₁)

-- Aliases for the above definitions that spell out their meaning:
_is-at-least-as-expressive-as_ = _≽_
_is-less-expressive-than_ = _⋡_
_is-more-expressive-than_ = _≻_
_is-equally-expressive-as_ = _≋_
```

> Note: The following proofs are highly similar to the respective proof for indexed sets.
> Maybe we could indeed reuse it here on a "higher index order".

```agda
≽-refl : Reflexive _≽_
≽-refl {x = L} e = e , ≣-refl L e

≽-trans : Transitive _≽_
≽-trans {L₁} {L₂} {L₃} L₂→L₁ L₃→L₂ {A} e₃ with L₃→L₂ {A} e₃
... | e₂ , e₃≣e₂ with L₂→L₁ {A} e₂
...   | e₁ , e₂≣e₁ = e₁ , ≣-trans {A} {L₃} {L₂} {L₁} {e₃} {e₂} {e₁} e₃≣e₂ e₂≣e₁

≽-antisym : Antisymmetric _≋_ _≽_
≽-antisym L₁≽L₂ L₂≽L₁ = L₁≽L₂ , L₂≽L₁

≋-refl : Reflexive _≋_
≋-refl {x} = ≽-refl {x} , ≽-refl {x}

≋-sym : Symmetric _≋_
≋-sym (L₁≽L₂ , L₂≽L₁) = L₂≽L₁ , L₁≽L₂

≋-trans : Transitive _≋_
≋-trans (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂)
  =   ≽-trans L₁≽L₂ L₂≽L₃
    , ≽-trans L₃≽L₂ L₂≽L₁
```

## Concluding expressiveness from translations

```agda
SemanticsPreserving : ∀ (L₁ L₂ : VariabilityLanguage V) → Expression L₁ ⇒ₚ Expression L₂ → Set₁
SemanticsPreserving L₁ L₂ t = ∀ {A} (e : Expression L₁ A) → L₁ , L₂ ⊢ e ≣ t e

expressiveness-by-translation : ∀ {L₁ L₂ : VariabilityLanguage V}
  → (t : Expression L₁ ⇒ₚ Expression L₂)
  → SemanticsPreserving L₁ L₂ t
  → L₂ ≽ L₁
expressiveness-by-translation t t-pres = λ e₂ → t e₂ , t-pres e₂ -- this implementation is very similar to ⊆[]→⊆
```
