```agda
open import Level using (Level; suc; _⊔_)
module Framework.FunctionLanguage where

open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive; Antisymmetric; DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_)
open import Function using (id; _∘_; Injective)
```

## Core definitions

The semantics of a function language is a function.
This means, for every expression in the language, we can
obtain the function that it describes.
```agda
FunctionSemantics : (Expression : Set) → (Input : Set) → (Output : Set) → Set
FunctionSemantics Expression Input Output = Expression → (Input → Output)
```

A set of expression constitutes a function language if it
has function semantics for a certain type of input values.
```agda
record FunctionLanguage (Output : Set) : Set₁ where
  constructor ⟪_,_,_⟫
  field
    Expression : Set
    Input      : Set
    Semantics  : FunctionSemantics Expression Input Output
open FunctionLanguage
```

## Translations

```agda
_⇒_ : Set → Set → Set
A ⇒ B = A → B

record _⇔_ (A B : Set) : Set where
  field
    to   : A ⇒ B
    from : B ⇒ A
open _⇔_ public

{-|
A translation t from a language L₁ to another language L₂
constitutes an embedding if there exists an inverse translation t⁻¹.
This means that all expressions in L₁ have a unique counterpart in
L₂ (i.e., the translation is injective).
-}
to-is-Embedding : ∀ {A B : Set} → A ⇔ B → Set
to-is-Embedding t = from t ∘ to t ≗ id

Embedding→Injective : ∀ {A B : Set}
  → (t : A ⇔ B)
  → to-is-Embedding t
  → Injective _≡_ _≡_ (to t)
Embedding→Injective t emb {x} {y} to-x≡to-y
  -- By congruence, we can wrap both sides of the equation in from.
  with Eq.cong (from t) to-x≡to-y
... | from-to-x≡from-to-y
      -- By embedding, we can cancel the from ∘ to terms on both sides.
      rewrite emb x | emb y
      = from-to-x≡from-to-y
```

## Comparing expressions of the same language

Two expressions `e₁` , `e₂` of the same language are semantically equivalent
if the functions they describe are pointwise equal (same output for same inputs):
```agda
private
  c = Level.0ℓ
  e = Level.0ℓ
module Comp
  {ℓ : Level}
  (O : Setoid c ℓ)
  where

  open Setoid O
  open import Data.IndexedSet O
    using
      (_⊆_; _≅_; _≐_
      ; ≐→≅
      ; ⊆-refl; ⊆-antisym; ⊆-trans
      ; ≅-refl;     ≅-sym; ≅-trans
      )
  -- Alias for the type of function languages over the give setoid.
  𝕃 = FunctionLanguage Carrier

  _⊢_≣₁_ : ∀ (L : 𝕃)
    → (e₁ e₂ : Expression L)
    → Set (ℓ)
  L ⊢ e₁ ≣₁ e₂ = ⟦ e₁ ⟧ ≐ ⟦ e₂ ⟧
    where
      ⟦_⟧ = Semantics L
  infix 5 _⊢_≣₁_

  ≣₁-IsEquivalence : ∀ {L : 𝕃} → IsEquivalence (L ⊢_≣₁_)
  ≣₁-IsEquivalence = record
    { refl  = λ _ → refl
    ; sym   = λ x≣y c → sym (x≣y c)
    ; trans = λ i≣j j≣k c → trans (i≣j c) (j≣k c)
    }
```

Syntactic equality implies semantic equality, independent of the semantics:
```agda
  ≡→≣₁ : ∀ {L : 𝕃} {a b : Expression L}
    → a ≡ b
      ----------
    → L ⊢ a ≣₁ b
  ≡→≣₁ eq c rewrite eq = refl
```

## Comparing expressions across languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.

```agda
  _,_⊢_≤_ :
    ∀ (L₁ L₂ : 𝕃)
    → Expression L₁
    → Expression L₂
    → Set ℓ
  L₁ , L₂ ⊢ e₁ ≤ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
    where
      ⟦_⟧₁ = Semantics L₁
      ⟦_⟧₂ = Semantics L₂
  infix 5 _,_⊢_≤_

  _,_⊢_≣_ :
    ∀ (L₁ L₂ : 𝕃)
    → Expression L₁
    → Expression L₂
    → Set ℓ
  L₁ , L₂ ⊢ e₁ ≣ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
    where
      ⟦_⟧₁ = Semantics L₁
      ⟦_⟧₂ = Semantics L₂
  infix 5 _,_⊢_≣_

  ≤-refl : ∀ (L : 𝕃) (e : Expression L)
    → L , L ⊢ e ≤ e
  ≤-refl _ _ = ⊆-refl

  ≤-antisym : ∀ {A B : 𝕃} {a : Expression A} {b : Expression B}
    → A , B ⊢ a ≤ b
    → B , A ⊢ b ≤ a
    → A , B ⊢ a ≣ b
  ≤-antisym = ⊆-antisym

  ≤-trans : ∀ {A B C : 𝕃}
              {a : Expression A} {b : Expression B} {c : Expression C}
    → A , B ⊢ a ≤ b
    → B , C ⊢ b ≤ c
      -------------
    → A , C ⊢ a ≤ c
  ≤-trans = ⊆-trans

  ≣-refl : ∀ (L : 𝕃) (e : Expression L)
      -------------
    → L , L ⊢ e ≣ e
  ≣-refl _ _ = ≅-refl

  ≣-sym : ∀ {A B : 𝕃} {a : Expression A} {b : Expression B}
    → A , B ⊢ a ≣ b
    → B , A ⊢ b ≣ a
  ≣-sym = ≅-sym

  ≣-trans : ∀ {A B C : 𝕃}
              {a : Expression A} {b : Expression B} {c : Expression C}
    → A , B ⊢ a ≣ b
    → B , C ⊢ b ≣ c
      -------------
    → A , C ⊢ a ≣ c
  ≣-trans = ≅-trans

  ≣₁→≣ : ∀ {L : 𝕃} {a b : Expression L}
    → L ⊢ a ≣₁ b
    → L , L ⊢ a ≣ b
  ≣₁→≣ = ≐→≅
```

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same function.
This means that there exists a translation from `L₂` to `L₁`, , thus `L₁` can model `L₂`:
```agda
  {-|
  Core expressiveness relation that constitutes a partial order of variability languages.
  L₁ ≽ L₂ reads as L₁ is at least as expressive as L₂.
  -}
  _≽_ : ∀ (L₁ L₂ : 𝕃) → Set (e ⊔ ℓ) --\succeq
  L₁ ≽ L₂ =
    ∀ (e₂ : Expression L₂) →
        (Σ[ e₁ ∈ Expression L₁ ] L₂ , L₁ ⊢ e₂ ≣ e₁)
    -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but first we have to generalize our multisets somehow to allow keys in the source set.

  _⋡_ : ∀ (L₁ L₂ : 𝕃) → Set (e ⊔ ℓ) -- \nsucceq
  L₁ ⋡ L₂ = ¬ (L₁ ≽ L₂)

  _≻_ : ∀ (L₁ L₂ : 𝕃) → Set (e ⊔ ℓ) -- \succ
  L₁ ≻ L₂ = L₁ ≽ L₂ × L₂ ⋡ L₁

  _≋_ : ∀ (L₁ L₂ : 𝕃) → Set (e ⊔ ℓ) --\~~~
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

## Concluding expressiveness from translations

```agda
  SemanticsPreserving : ∀ (L₁ L₂ : 𝕃) → Expression L₁ ⇒ Expression L₂ → Set (e ⊔ ℓ)
  SemanticsPreserving L₁ L₂ t = ∀ (e : Expression L₁) → L₁ , L₂ ⊢ e ≣ t e

  expressiveness-by-translation : ∀ {L₁ L₂ : 𝕃}
    → (t : Expression L₁ ⇒ Expression L₂)
    → SemanticsPreserving L₁ L₂ t
    → L₂ ≽ L₁
  expressiveness-by-translation t t-pres = λ e₁ → t e₁ , t-pres e₁ -- this implementation is very similar to ⊆[]→⊆
```
