```agda
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive; Antisymmetric)
module Framework.V2.FunctionLanguage
  {c ℓ : Level}
  (O : Setoid c ℓ)
  where

open import Data.Product using (_,_; _×_; Σ-syntax)
open import Function using (id; _∘_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

open Setoid O
open import Data.IndexedSet O
  using
    (_⊆_; _≅_; _≐_
    ; ⊆-refl; ⊆-antisym; ⊆-trans
    ; ≅-refl;     ≅-sym; ≅-trans
    )
```

## Core definitions

The semantics of a function language is a function.
This means, for every expression in the language, we can
obtain the function that it describes.
```agda
FunctionSemantics : ∀ (Expression : Set c) → (Input : Set c) → Set c
FunctionSemantics Expression Input = Expression → (Input → Carrier)
```

A set of expression constitutes a function language if it
has function semantics for a certain type of input values.
```agda
record FunctionLanguage : Set (suc c) where
  constructor ⟪_,_,_⟫
  field
    Expression : Set c
    Input      : Set c
    Semantics  : FunctionSemantics Expression Input
open FunctionLanguage public
```

## Comparing expressions of the same language

Two expressions `e₁` , `e₂` of the same language are semantically equivalent
if the functions they describe are pointwise equal (same output for same inputs):
```agda
_⊢_≣₁_ : ∀ (L : FunctionLanguage)
  → (e₁ e₂ : Expression L)
  → Set (c ⊔ ℓ)
L ⊢ e₁ ≣₁ e₂ = ⟦ e₁ ⟧ ≐ ⟦ e₂ ⟧
  where
    ⟦_⟧ = Semantics L
infix 5 _⊢_≣₁_

≣₁-IsEquivalence : ∀ {L : FunctionLanguage} → IsEquivalence (L ⊢_≣₁_)
≣₁-IsEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ x≣y c → sym (x≣y c)
  ; trans = λ i≣j j≣k c → trans (i≣j c) (j≣k c)
  }
```

Syntactic equality implies semantic equality, independent of the semantics:
```agda
≡→≣ : ∀ {L : FunctionLanguage} {a b : Expression L}
  → a ≡ b
    ----------
  → L ⊢ a ≣₁ b
≡→≣ eq c rewrite eq = refl
```

## Comparing expressions across languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.

```agda
_,_⊢_≤_ :
  ∀ (L₁ L₂ : FunctionLanguage)
  → Expression L₁
  → Expression L₂
  → Set (c ⊔ ℓ)
L₁ , L₂ ⊢ e₁ ≤ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂
infix 5 _,_⊢_≤_

_,_⊢_≣_ :
  ∀ (L₁ L₂ : FunctionLanguage)
  → Expression L₁
  → Expression L₂
  → Set (c ⊔ ℓ)
L₁ , L₂ ⊢ e₁ ≣ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂
infix 5 _,_⊢_≣_

≤-refl : ∀ (L : FunctionLanguage) (e : Expression L)
  → L , L ⊢ e ≤ e
≤-refl _ _ = ⊆-refl

≤-antisym : ∀ {A B : FunctionLanguage} {a : Expression A} {b : Expression B}
  → A , B ⊢ a ≤ b
  → B , A ⊢ b ≤ a
  → A , B ⊢ a ≣ b
≤-antisym = ⊆-antisym

≤-trans : ∀ {A B C : FunctionLanguage}
            {a : Expression A} {b : Expression B} {c : Expression C}
  → A , B ⊢ a ≤ b
  → B , C ⊢ b ≤ c
    -------------
  → A , C ⊢ a ≤ c
≤-trans = ⊆-trans

≣-refl : ∀ (L : FunctionLanguage) (e : Expression L)
    -------------
  → L , L ⊢ e ≣ e
≣-refl _ _ = ≅-refl

≣-sym : ∀ {A B : FunctionLanguage} {a : Expression A} {b : Expression B}
  → A , B ⊢ a ≣ b
  → B , A ⊢ b ≣ a
≣-sym = ≅-sym

≣-trans : ∀ {A B C : FunctionLanguage}
            {a : Expression A} {b : Expression B} {c : Expression C}
  → A , B ⊢ a ≣ b
  → B , C ⊢ b ≣ c
    -------------
  → A , C ⊢ a ≣ c
≣-trans = ≅-trans
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same function.
This means that there exists a translation from `L₂` to `L₁`, , thus `L₁` can model `L₂`:
```agda
{-|
Core expressiveness relation that constitutes a partial order of variability languages.
L₁ ≽ L₂ reads as L₁ is at least as expressive as L₂.
-}
_≽_ : ∀ (L₁ L₂ : FunctionLanguage) → Set (c ⊔ ℓ) --\succeq
L₁ ≽ L₂ =
  ∀ (e₂ : Expression L₂) →
      (Σ[ e₁ ∈ Expression L₁ ] L₂ , L₁ ⊢ e₂ ≣ e₁)
  -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but first we have to generalize our multisets somehow to allow keys in the source set.

_⋡_ : ∀ (L₁ L₂ : FunctionLanguage) → Set (c ⊔ ℓ) -- \nsucceq
L₁ ⋡ L₂ = ¬ (L₁ ≽ L₂)

_≻_ : ∀ (L₁ L₂ : FunctionLanguage) → Set (c ⊔ ℓ) -- \succ
L₁ ≻ L₂ = L₁ ≽ L₂ × L₂ ⋡ L₁

_≋_ : ∀ (L₁ L₂ : FunctionLanguage) → Set (c ⊔ ℓ) --\~~~
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
≽-trans L₂→L₁ L₃→L₂ e₃ =
  let e₂ , e₃≚e₂ = L₃→L₂ e₃
      e₁ , e₂≚e₁ = L₂→L₁ e₂
   in e₁ , ≅-trans e₃≚e₂ e₂≚e₁

≽-antisym : Antisymmetric _≋_ _≽_
≽-antisym L₁≽L₂ L₂≽L₁ = L₁≽L₂ , L₂≽L₁

≋-refl : Reflexive _≋_
≋-refl = ≽-refl , ≽-refl

≋-sym : Symmetric _≋_
≋-sym (L₁≽L₂ , L₂≽L₁) = L₂≽L₁ , L₁≽L₂

≋-trans : Transitive _≋_
≋-trans (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂)
  =   ≽-trans L₁≽L₂ L₂≽L₃
    , ≽-trans L₃≽L₂ L₂≽L₁
```

## Translations

```agda
_⇒_ : (L₁ L₂ : FunctionLanguage) → Set c
L₁ ⇒ L₂ = Expression L₁ → Expression L₂

record _⇔_ (L₁ L₂ : FunctionLanguage) : Set c where
  field
    to   : L₁ ⇒ L₂
    from : L₂ ⇒ L₁
open _⇔_ public

Embedding : ∀ {A B : FunctionLanguage} → A ⇔ B → Set c
Embedding {A} {B} t = from t ∘ to t ≗ id

SemanticsPreserving : ∀ (L₁ L₂ : FunctionLanguage) → L₁ ⇒ L₂ → Set (c ⊔ ℓ)
SemanticsPreserving L₁ L₂ t = ∀ (e : Expression L₁) → L₁ , L₂ ⊢ e ≣ t e

expressiveness-by-translation : ∀ {L₁ L₂ : FunctionLanguage}
  → (t : L₁ ⇒ L₂)
  → SemanticsPreserving L₁ L₂ t
  → L₂ ≽ L₁
expressiveness-by-translation t t-pres = λ e₁ → t e₁ , t-pres e₁ -- this implementation is very similar to ⊆[]→⊆
```
