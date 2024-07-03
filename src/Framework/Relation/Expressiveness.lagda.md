```agda
open import Framework.Definitions
module Framework.Relation.Expressiveness (V : 𝕍) where

open import Data.EqIndexedSet using (≅[]→≅)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Relation.Binary using (IsEquivalence; IsPartialOrder; Reflexive; Symmetric; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans)
open import Function using (_∘_; Injective)

open import Framework.VariabilityLanguage
open import Framework.Relation.Expression V
open import Framework.Relation.Function using (_⇒ₚ_)
open import Framework.Compiler
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same function.
This means that there exists a translation from `L₂` to `L₁`, , thus `L₁` can model `L₂`:
```agda
{-|
Our central expressiveness relation.
L₁ ≽ L₂ reads as: L₁ is at least as expressive as L₂.
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

≋-IsEquivalence : IsEquivalence _≋_
≋-IsEquivalence = record
  { refl = ≋-refl
  ; sym = ≋-sym
  ; trans = ≋-trans
  }

≽-IsPartialOrder : IsPartialOrder _≋_ _≽_
≽-IsPartialOrder = record
  { isPreorder = record
    { isEquivalence = ≋-IsEquivalence
    ; reflexive = proj₁
    ; trans = ≽-trans
    }
  ; antisym = ≽-antisym
  }

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

expressiveness-from-compiler : ∀ {L₁ L₂ : VariabilityLanguage V}
  → LanguageCompiler L₁ L₂
  → L₂ ≽ L₁
expressiveness-from-compiler compiler = expressiveness-by-translation (LanguageCompiler.compile compiler) (λ e → ≅[]→≅ (LanguageCompiler.preserves compiler e))

{-
Since Agda is based on constructive logic,
any proof of existence explicitly constructs the element
in questions. Hence, from a proof of expressiveness,
we can always use the constructed elements (expressions and configurations)
to be the result of a compiler.
-}
compiler-from-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage V}
  → L₂ ≽ L₁
  → LanguageCompiler L₁ L₂
compiler-from-expressiveness {L₁} {L₂} exp = record
  { compile         = proj₁ ∘ exp
  ; config-compiler = λ e → record { to = conf e ; from = fnoc e }
  ; preserves       = λ e → ⊆-conf e , ⊆-fnoc e
  }
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂
    open import Data.EqIndexedSet

    conf : ∀ {A} → Expression L₁ A → Config L₁ → Config L₂
    conf e c₁ = proj₁ (proj₁ (proj₂ (exp e)) c₁)

    fnoc : ∀ {A} → Expression L₁ A → Config L₂ → Config L₁
    fnoc e c₂ = proj₁ (proj₂ (proj₂ (exp e)) c₂)

    eq : ∀ {A} → (e : Expression L₁ A) → ⟦ e ⟧₁ ≅ ⟦ proj₁ (exp e) ⟧₂
    eq e = proj₂ (exp e)

    ⊆-conf : ∀ {A} → (e : Expression L₁ A) → ⟦ e ⟧₁ ⊆[ conf e ] ⟦ proj₁ (exp e) ⟧₂
    ⊆-conf e with eq e
    ... | ⊆ , _ = proj₂ ∘ ⊆

    ⊆-fnoc : ∀ {A} → (e : Expression L₁ A) → ⟦ proj₁ (exp e) ⟧₂ ⊆[ fnoc e ] ⟦ e ⟧₁
    ⊆-fnoc e with eq e
    ... | _ , ⊇ = proj₂ ∘ ⊇

compiler-cannot-exist : ∀ {L₁ L₂ : VariabilityLanguage V}
  → L₂ ⋡ L₁
  → LanguageCompiler L₁ L₂
  → ⊥
compiler-cannot-exist = contraposition expressiveness-from-compiler
```
