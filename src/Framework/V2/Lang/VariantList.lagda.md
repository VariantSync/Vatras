# Lists of Variants are Also Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Framework.V2.Definitions
module Framework.V2.Lang.VariantList (Variant : 𝕍) where
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

open import Util.List using (find-or-last)

import Data.IndexedSet

-- open import Framework.Definitions
import Framework.V2.Variant
```

## Definitions

```agda
VariantList : 𝔼
VariantList A = List⁺ (Variant A)

-- it would be nice if the confLang would be parameterized in expressions
Configuration : 𝕊
Configuration = ℕ

-- ⟦_⟧ : ∀ {i : Size} {A : 𝔸} → VariantList i A → Configuration → Variant i A
⟦_⟧ : 𝔼-Semantics Variant Configuration VariantList
⟦_⟧ e c = find-or-last c e

VariantListL : VariabilityLanguage Variant
VariantListL = Lang-⟪ VariantList , Configuration , ⟦_⟧ ⟫
```

## Properties

### Completeness

```agda
open import Framework.V2.V1Compat

-- prove completeness via inference rules
module Complete (A : 𝔸) where
  open Framework.V2.Variant Variant A
  open IVSet using (_≅_; _⊆[_]_; ≅[]→≅)
  open import Util.AuxProofs using (clampAt)

  private
    variable
      n : ℕ
      e : VariantList A

  -- rules for translating a set of variants to a list of variants
  infix 3 _⊢_⟶_
  data _⊢_⟶_ : (n : ℕ) → VMap n → VariantList A → Set where
    -- a singleton set is translated to a singleton list
    E-zero : ∀ {V : VMap zero}
        ------------------------
      → zero ⊢ V ⟶ V zero ∷ []

    {-|
    For a set V with more than one variant, we:
    - put the first variant into our list
    - remove that first variant from our set of variants
    - translate the rest recursively.
    -}
    E-suc : ∀ {V : VMap (suc n)}
      → n ⊢ remove-first V ⟶ e
        -------------------------------
      → suc n ⊢ V ⟶ V zero ∷ toList e

  {-| Proof that the encoding is deterministic -}
  determinism : ∀ {e₁ e₂ : VariantList A} {V : VMap n}
    → n ⊢ V ⟶ e₁
    → n ⊢ V ⟶ e₂
      -----------------
    → e₁ ≡ e₂
  determinism E-zero E-zero = refl
  determinism (E-suc l) (E-suc r) rewrite determinism l r = refl

  -- smart constructor for totality proofs
  -- makes the implicit result expression e explicit
  return : ∀ {V : VMap n}
    →         n ⊢ V ⟶ e
      --------------------
    → ∃[ e ] (n ⊢ V ⟶ e)
  return {e = e} ⟶e = e , ⟶e

  {-| Proof that the encoding is total and thus can be computed. -}
  total :
    ∀ (V : VMap n)
      --------------------
    → ∃[ e ] (n ⊢ V ⟶ e)
  total {n = zero}  vs = return E-zero
  total {n = suc n} vs = return (E-suc (proj₂ (total (remove-first vs))))

  {-| Encodes a set of variants into a list of variants. -}
  encode : ∀ (V : VMap n) → VariantList A
  encode = proj₁ ∘ total

  -- translate configs

  vl-conf : Fin (suc n) → Configuration
  vl-conf i = toℕ i

  vl-fnoc : Configuration → Fin (suc n)
  vl-fnoc {n} c = clampAt n c

  -- proof of preservation

  preserves-∈ : ∀ {V}
    → n ⊢ V ⟶ e
      -----------------
    → V ⊆[ vl-conf ] ⟦ e ⟧
  preserves-∈ E-zero    zero = refl

  preserves-∈ (E-suc _) zero = refl
  preserves-∈ (E-suc ⟶e) (suc i) = preserves-∈ ⟶e i

  preserves-∋ : ∀ {V}
    → n ⊢ V ⟶ e
      -----------------
    → ⟦ e ⟧ ⊆[ vl-fnoc ] V
  preserves-∋ E-zero      zero   = refl
  preserves-∋ E-zero     (suc _) = refl
  preserves-∋ (E-suc  _)  zero   = refl
  preserves-∋ (E-suc ⟶e) (suc c) = preserves-∋ ⟶e c

  preserves : ∀ {V}
    → n ⊢ V ⟶ e
      ----------
    → V ≅ ⟦ e ⟧
  preserves encoding = ≅[]→≅ (preserves-∈ encoding , preserves-∋ encoding)

VariantList-is-Complete : Complete VariantListL
VariantList-is-Complete {A} vs =
  let open Complete A
      e , derivation = total vs
   in e , preserves derivation
```

### Soundness

```text
open import Framework.Properties.Soundness
open import Framework.Proof.Soundness using (soundness-by-finite-semantics)
open import Framework.Relation.Configuration using (_⊢_≣ᶜ_)

module Finity (A : 𝔸) where
  open Data.List.NonEmpty using (length)
  open import Function using (Surjective)

  open Complete A using (vl-conf; vl-fnoc)

  #' : Expression VariantListL → ℕ
  #' = length

  pick-conf : (e : Expression A VariantListL) → Fin (suc (#' e)) → Configuration
  pick-conf _ = conf

  pick-conf-surjective : ∀ (e : Expression VariantListL) → Surjective _≡_ (e ⊢_≣ᶜ_) (pick-conf e)
  pick-conf-surjective _ zero = zero , refl
  pick-conf-surjective [ _ ∷ [] ] (suc y) = fnoc (suc y) , refl
  pick-conf-surjective [ e ∷ f ∷ es ] (suc y) with pick-conf-surjective [ f ∷ es ] y
  ... | i , ⟦f∷es⟧i≡⟦f∷es⟧y = suc i , ⟦f∷es⟧i≡⟦f∷es⟧y

VariantList-is-Sound : Sound VariantListL
VariantList-is-Sound = soundness-by-finite-semantics (λ {A} e →
      let open Finity A in
      record
      { size = #' e
      ; enumerate = pick-conf e
      ; enumerate-is-surjective = pick-conf-surjective e
      })
```

