# Lists of Variants are Also Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsEquivalence)
open import Framework.Definitions
module Lang.VariantList (V : 𝕍) where
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

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open Relation.Binary using (Setoid)

import Data.IndexedSet
open import Util.List using (find-or-last)

open import Framework.Definitions
import Framework.Variant
open import Framework.VariabilityLanguage
```

## Definitions

```agda
VariantList : 𝔼
VariantList A = List⁺ (V A)

-- it would be nice if the confLang would be parameterized in expressions
Configuration : 𝕊
Configuration = ℕ

-- ⟦_⟧ : ∀ {i : Size} {A : 𝔸} → VariantList i A → Configuration → Variant i A
⟦_⟧ : 𝔼-Semantics V Configuration VariantList
⟦_⟧ e c = find-or-last c e

VariantListL : VariabilityLanguage V
VariantListL = Lang-⟪ VariantList , Configuration , ⟦_⟧ ⟫
```

## Properties

### Completeness

```agda
-- prove completeness via inference rules
open import Util.AuxProofs using (clampAt)

private
  open Framework.Variant V
  variable
    n : ℕ
    A : 𝔸
    e : VariantList A

-- rules for translating a set of variants to a list of variants
infix 3 _⊢_⟶_
data _⊢_⟶_ : ∀ (n : ℕ) → VMap A n → VariantList A → Set where
  -- a singleton set is translated to a singleton list
  E-zero : ∀ {A} {V : VMap A zero}
      ------------------------
    → zero ⊢ V ⟶ V zero ∷ []

  {-|
  For a set V with more than one variant, we:
  - put the first variant into our list
  - remove that first variant from our set of variants
  - translate the rest recursively.
  -}
  E-suc : ∀ {V : VMap A (suc n)}
    → n ⊢ remove-first A V ⟶ e
      -------------------------------
    → suc n ⊢ V ⟶ V zero ∷ toList e

{-| Proof that the encoding is deterministic -}
determinism : ∀ {e₁ e₂ : VariantList A} {V : VMap A n}
  → n ⊢ V ⟶ e₁
  → n ⊢ V ⟶ e₂
    -----------------
  → e₁ ≡ e₂
determinism E-zero E-zero = Eq.refl
determinism (E-suc l) (E-suc r) rewrite determinism l r = Eq.refl

-- smart constructor for totality proofs
-- makes the implicit result expression e explicit
return : ∀ {V : VMap A n}
  →         n ⊢ V ⟶ e
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
return {e = e} ⟶e = e , ⟶e

{-| Proof that the encoding is total and thus can be computed. -}
total :
  ∀ (V : VMap A n)
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
total {n = zero}  vs = return E-zero
total {n = suc n} vs = return (E-suc (proj₂ (total (remove-first _ vs))))

{-| Encodes a set of variants into a list of variants. -}
encode : VMap A n → VariantList A
encode = proj₁ ∘ total

-- translate configs

vl-conf : Fin (suc n) → Configuration
vl-conf i = toℕ i

vl-fnoc : Configuration → Fin (suc n)
vl-fnoc {n} c = clampAt n c

-- proof of preservation

module _ {A : 𝔸} where
  open Data.IndexedSet (VariantSetoid A) using (_≅_; _⊆[_]_; ≅[]→≅)
  open Setoid (VariantSetoid A)

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

open import Framework.Variability.Completeness V using (Complete)

VariantList-is-Complete : Complete VariantListL
VariantList-is-Complete {A} vs =
  let e , derivation = total vs
  in  e , preserves derivation
```

### Soundness

```agda
open import Framework.Variability.Soundness V using (Sound)
open import Framework.Function.Properties.Finity VariantSetoid using (soundness-from-enumerability)
open import Framework.Function.Relation.Index VariantSetoid using (_∋_⊢_≣ⁱ_)
open Data.List.NonEmpty using (length)
open Function using (Surjective)

module _ {A : 𝔸} where
  open Setoid (VariantSetoid A)

  #' : VariantList A → ℕ
  #' = length

  pick-conf : (e : VariantList A) → Fin (suc (#' e)) → Configuration
  pick-conf _ = vl-conf

  pick-conf-surjective : ∀ (e : VariantList A) → Surjective _≡_ (VariantListL ∋ e ⊢_≣ⁱ_) (pick-conf e)
  pick-conf-surjective _ zero = zero , refl
  pick-conf-surjective (_ ∷ []) (suc y) = vl-fnoc (suc y) , refl
  pick-conf-surjective (e ∷ f ∷ es) (suc y) with pick-conf-surjective (f ∷ es) y
  ... | i , ⟦f∷es⟧i≡⟦f∷es⟧y = suc i , ⟦f∷es⟧i≡⟦f∷es⟧y

VariantList-is-Sound : Sound VariantListL
VariantList-is-Sound = soundness-from-enumerability (λ e → record
  { size = #' e
  ; enumerate = pick-conf e
  ; enumerate-is-surjective = pick-conf-surjective e
  })

```
