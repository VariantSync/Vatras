# Expressiveness of Languages for Static Variability

```agda
open import Vatras.Framework.Definitions
module Vatras.Framework.Relation.Expressiveness (V : 𝕍) where

open import Vatras.Data.EqIndexedSet using (≅[]→≅)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans)
open import Function using (_∘_; Injective)

open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Relation.Expression V
open import Vatras.Framework.Relation.Function using (_⇒ₚ_)
open import Vatras.Framework.Compiler
```

This module contains the basic definition of (relative) expressiveness `_≽_`,
as well as a range of related relations `_≻_`, `_⋡_`, and proves relevant properties.
We also show that compilers for variability languages can be used as proofs
of expressiveness and vice versa (because Agda uses constructive logic).

We say that a language `L₁` is as expressive as another language `L₂` if for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same variant generator.
```agda
{-|
Our central expressiveness relation.
L₁ ≽ L₂ reads as: L₁ is at least as expressive as L₂.
-}
_≽_ : ∀ (L M : VariabilityLanguage V) → Set₁ --\succeq
L ≽ M =
  ∀ {A : 𝔸} (m : Expression M A) →
      (Σ[ l ∈ Expression L A ] M , L ⊢ m ≣ l)

{-|
Negation of _≽_:
L ⋡ M means that L is not at least as expressive as M.
This means that there are expressions in M that denote things that cannot be expressed by L.
-}
_⋡_ : ∀ (L M : VariabilityLanguage V) → Set₁ -- \nsucceq
L ⋡ M = ¬ (L ≽ M)

{-|
L ≻ M means that L is more expressive than M.
This means that L can say everything M can say but not vice versa.
-}
_≻_ : ∀ (L M : VariabilityLanguage V) → Set₁ -- \succ
L ≻ M = L ≽ M × M ⋡ L

{-|
Expressive equality:
Two languages L ≋ M have the same semantic domain.
-}
_≋_ : ∀ (L M : VariabilityLanguage V) → Set₁ --\~~~
L ≋ M = (L ≽ M) × (M ≽ L)

-- Aliases for the above definitions that spell out their meaning:
_is-at-least-as-expressive-as_ = _≽_
_is-less-expressive-than_ = _⋡_
_is-more-expressive-than_ = _≻_
_is-equally-expressive-as_ = _≋_
```

We now prove that:
- `_≽_` is a partial order,
- `_≋_` is an equivalence relation
- `_≻_` is a strict partial order

> Note: Some of the following proofs are similar to the respective proof for indexed sets.
> Maybe we could indeed reuse it here on a "higher index order" later on.

```agda
≽-refl : Reflexive _≽_
≽-refl {x = L} e = e , ≣-refl L e

≽-trans : Transitive _≽_
≽-trans {L} {M} {N} M→L N→M {A} n with N→M n
... | m , n≣m with M→L m
...   | l , m≣l = l , ≣-trans {A} {N} {M} {L} n≣m m≣l

≽-antisym : Antisymmetric _≋_ _≽_
≽-antisym L≽M M≽L = L≽M , M≽L

≋-refl : Reflexive _≋_
≋-refl {x} = ≽-refl {x} , ≽-refl {x}

≋-sym : Symmetric _≋_
≋-sym (L≽M , M≽L) = M≽L , L≽M

≋-trans : Transitive _≋_
≋-trans (L≽M , M≽L) (M≽N , N≽M) = ≽-trans L≽M M≽N , ≽-trans N≽M M≽L

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

≻-trans : Transitive _≻_
≻-trans {L} {M} {N} (L≽M , M⋡L) (M≽N , N⋡M) = ≽-trans L≽M M≽N , λ N≽L → M⋡L (≽-trans M≽N N≽L)

≻-irrefl : Irreflexive _≋_ _≻_
≻-irrefl {L} {M} (L≽M , M≽L) (_ , M⋡L) = M⋡L M≽L

≻-Respectsʳ-≋ : _≻_ Respectsʳ _≋_
≻-Respectsʳ-≋ {L} {M} {N} (M≽N , _) (L≽M , M⋡L) = ≽-trans L≽M M≽N , λ N≽L → M⋡L (≽-trans M≽N N≽L)

≻-Respectsˡ-≋ : _≻_ Respectsˡ _≋_
≻-Respectsˡ-≋ {L} {M} {N} (_ , N≽M) (M≽L , L⋡M) = ≽-trans N≽M M≽L , λ L≽N → L⋡M (≽-trans L≽N N≽M)

≻-Respects-≋ : _≻_ Respects₂ _≋_
≻-Respects-≋ = ≻-Respectsʳ-≋ , ≻-Respectsˡ-≋

≻-IsStrictPartialOrder : IsStrictPartialOrder _≋_ _≻_
≻-IsStrictPartialOrder = record
  { isEquivalence = ≋-IsEquivalence
  ; irrefl = ≻-irrefl
  ; trans = ≻-trans
  ; <-resp-≈ = ≻-Respects-≋
  }
```

## Proving Expressiveness by Compilation

```agda
{-|
A translation of expressions preserves semantics if
the translated expression denotes the same variant generator as the initial expression.
-}
SemanticsPreserving : ∀ (L M : VariabilityLanguage V) → Expression L ⇒ₚ Expression M → Set₁
SemanticsPreserving L M t = ∀ {A} (e : Expression L A) → L , M ⊢ e ≣ t e

{-|
A semantics preserving translation is a proof of expressiveness.
-}
expressiveness-by-translation : ∀ {L M : VariabilityLanguage V}
  → (t : Expression L ⇒ₚ Expression M)
  → SemanticsPreserving L M t
    ----------------------------------
  → M ≽ L
expressiveness-by-translation t t-pres = λ e₂ → t e₂ , t-pres e₂ -- this implementation is very similar to ⊆[]→⊆

{-|
From a compiler of a variability language,
we can prove expressiveness.
A compiler here, is basically an alternative definition of a semantics
preserving translation but it provides more detail on how the translation
is performed.
-}
expressiveness-from-compiler : ∀ {L M : VariabilityLanguage V}
  → LanguageCompiler L M
    --------------------
  → M ≽ L
expressiveness-from-compiler compiler = expressiveness-by-translation (LanguageCompiler.compile compiler) (λ e → ≅[]→≅ (LanguageCompiler.preserves compiler e))

{-|
Since Agda is based on constructive logic,
any proof of existence explicitly constructs the element
in questions. Hence, from a proof of expressiveness,
we can always use the constructed elements (expressions and configurations)
to be the result of a compiler.
-}
compiler-from-expressiveness : ∀ {L M : VariabilityLanguage V}
  → M ≽ L
    --------------------
  → LanguageCompiler L M
compiler-from-expressiveness {L} {M} exp = record
  { compile         = proj₁ ∘ exp
  ; config-compiler = λ e → record
    { to   = ⊆-index (proj₁ (proj₂ (exp e)))
    ; from = ⊆-index (proj₂ (proj₂ (exp e)))
    }
  ; preserves       = ≅→≅[] ∘ proj₂ ∘ exp
  }
  where
    open import Vatras.Data.EqIndexedSet

{-|
When M is not at least as expressive as L,
then L can never be compiled to M.
The intuition is that there are expressions in L
that cannot be expressed in M.
-}
compiler-cannot-exist : ∀ {L M : VariabilityLanguage V}
  → M ⋡ L
  → LanguageCompiler L M
    --------------------
  → ⊥
compiler-cannot-exist = contraposition expressiveness-from-compiler
```
