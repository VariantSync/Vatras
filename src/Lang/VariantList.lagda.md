# Lists of Variants are Also Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.VariantList where
```

## Imports

```agda
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using ([]; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Definitions
```

## Definitions

```agda
VariantList : VarLang
VariantList i A = List⁺ (Variant i A)

VList : ∀ (A : Domain) → Set
VList = VariantList ∞

-- it would be nice if the confLang would be parameterized in expressions
Configuration : ConfLang
Configuration = ℕ

find : ∀ {A : Set} → List⁺ A → ℕ → A
find (x ∷ xs)        zero = x
find (x ∷ [])     (suc n) = x
find (x ∷ y ∷ ys) (suc n) = find (y ∷ ys) n

must-take-whats-left : ∀ {A : Set} {x : A}
 → (i : ℕ)
 → find (x ∷ []) i ≡ x
must-take-whats-left zero = refl
must-take-whats-left (suc i) = refl

-- ⟦_⟧ : ∀ {i : Size} {A : Domain} → VariantList i A → Configuration → Variant i A
⟦_⟧ : Semantics VariantList Configuration
⟦_⟧ = find

VariantListL : VariabilityLanguage
VariantListL = record
  { expression    = VariantList
  ; configuration = Configuration
  ; semantics     = ⟦_⟧
  }
```

## Properties

### Completeness

```agda
open import Lang.Properties.Completeness

-- prove completeness via inference rules
module Complete (A : Domain) where
  open import Data.Multiset (VariantSetoid ∞ A) using (_≅_; ⊆-by-index-translation)

  private
    variable
      n : ℕ
      V : VSet A n
      e : VList A

  -- rules for translating a set of variants to a list of variants
  infix 3 _⊢_⟶_
  data _⊢_⟶_ : (n : ℕ) → VSet A n → VList A → Set where
    -- a singleton set is translated to a singleton list
    E-zero :
        ------------------------
        zero ⊢ V ⟶ V zero ∷ []

    {-|
    For a set V with more than one variant, we:
    - put the first variant into our list
    - remove that first variant from our set of variants
    - translate the rest recursively.
    -}
    E-suc : ∀ {V : VSet A (suc n)}
      → n ⊢ (forget-first V) ⟶ e
        -------------------------------
      → suc n ⊢ V ⟶ V zero ∷ toList e

  {-| Proof that the encoding is deterministic -}
  determinism : ∀ {e₁ e₂ : VList A}
    → n ⊢ V ⟶ e₁
    → n ⊢ V ⟶ e₂
      -----------------
    → e₁ ≡ e₂
  determinism E-zero E-zero = refl
  determinism (E-suc l) (E-suc r) rewrite determinism l r = refl

  -- smart constructor for totality proofs
  -- makes the implicit result expression e explicit
  return :
              n ⊢ V ⟶ e
      --------------------
    → ∃[ e ] (n ⊢ V ⟶ e)
  return {e = e} ⟶e = e , ⟶e

  {-| Proof that the encoding is total and thus can be computed. -}
  total :
    ∀ (V : VSet A n)
      --------------------
    → ∃[ e ] (n ⊢ V ⟶ e)
  total {n = zero}  vs = return E-zero
  total {n = suc n} vs = return (E-suc (proj₂ (total (forget-first vs))))

  {-| Encodes a set of variants into a list of variants. -}
  encode : ∀ (V : VSet A n) → VList A
  encode = proj₁ ∘ total

  -- translate configs

  conf : Fin (suc n) → Configuration
  conf i = toℕ i

  fnoc : Configuration → Fin (suc n)
  fnoc zero = zero
  fnoc {zero} (suc _) = zero
  fnoc {suc n} (suc c) = suc (fnoc {n} c)

  -- proof of preservation

  preserves-∈ :
      n ⊢ V ⟶ e
    → (i : Fin (suc n))
      --------------------
    → V i ≡ ⟦ e ⟧ (conf i)
  preserves-∈ E-zero    zero = refl
  preserves-∈ (E-suc _) zero = refl
  preserves-∈ {V = V} (E-suc {n = n} {e = e} ⟶e) (suc i) =
    begin
      V (suc i)
    ≡⟨⟩
      (forget-first V) i
    ≡⟨ preserves-∈ ⟶e i ⟩
      ⟦ e ⟧ (conf i)
    ≡⟨⟩
      ⟦ V zero ∷ toList e ⟧ (suc (conf i))
    ≡⟨⟩
      ⟦ V zero ∷ toList e ⟧ (conf (suc i))
    ∎

  preserves-∋ :
      n ⊢ V ⟶ e
    → (c : Configuration)
      --------------------
    → ⟦ e ⟧ c ≡ V (fnoc c)
  preserves-∋ E-zero    zero    = refl
  preserves-∋ E-zero    (suc _) = refl
  preserves-∋ (E-suc _) zero    = refl
  preserves-∋ {V = V} (E-suc {n = n} {e = e} ⟶e) (suc c) =
    begin
      ⟦ V zero ∷ toList e ⟧ (suc c)
    ≡⟨⟩
      ⟦ e ⟧ c
    ≡⟨ preserves-∋ ⟶e c ⟩
      (forget-first V) (fnoc c)
    ≡⟨⟩
      V (suc (fnoc c))
    ≡⟨⟩
      V (fnoc (suc c))
    ∎

  preserves :
      n ⊢ V ⟶ e
      -----------
    → V ≅ ⟦ e ⟧
  preserves encoding =
      ⊆-by-index-translation conf (preserves-∈ encoding)
    , ⊆-by-index-translation fnoc (preserves-∋ encoding)

VariantList-is-Complete : Complete VariantListL
VariantList-is-Complete {A} vs =
  let open Complete A
      e , derivation = total vs
   in fromExpression VariantListL e , preserves derivation
```

### Soundness

```agda
open import Lang.Properties.Soundness

module Finity (A : Domain) where
  open Data.List.NonEmpty using (length)
  open import Function using (Surjective)

  open import Relations.Semantic using (_⊢_≣ᶜ_)
  open Complete A using (conf; fnoc)

  #' : VList A → ℕ
  #' = length

  pick-conf : (e : VList A) → Fin (suc (#' e)) → Configuration
  pick-conf _ = conf

  pick-conf-surjective : ∀ {e : Expression A VariantListL} → Surjective _≡_ (e ⊢_≣ᶜ_) (pick-conf (get e))
  pick-conf-surjective zero = zero , refl
  pick-conf-surjective {e = record { size = size₁ ; get = e ∷ [] }} (suc y) = fnoc (suc y) , refl
  pick-conf-surjective {e = record { size = size₁ ; get = e ∷ f ∷ es }} (suc y) with pick-conf-surjective {e = record {get = f ∷ es }} y
  ... | i , ⟦f∷es⟧i≡⟦f∷es⟧y = suc i , ⟦f∷es⟧i≡⟦f∷es⟧y

VariantList-is-Sound : Sound VariantListL
VariantList-is-Sound A =
  let open Finity A in
  record
  { # = #' ∘ get
  ; pick = pick-conf ∘ get
  ; pick-surjective = pick-conf-surjective
  }
```



