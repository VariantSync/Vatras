# Lists of Variants are Also Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.VariantList where
```

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList; _⁺∷ʳ_; _∷ʳ_)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Definitions

open import Util.AuxProofs using (clamp)
open import Util.List using (lookup-clamped)
```

## Definitions

```agda
VariantList : VarLang
VariantList i A = List⁺ (Variant i A)

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

```agda


lookup-clamped-zeroʳ : ∀ {A : Set} (xs : List⁺ A) (x : A) →
    lookup-clamped zero (xs ⁺∷ʳ x)
  ≡ lookup-clamped zero xs
lookup-clamped-zeroʳ = {!!}

open import Data.Product using (_,_)
open import Lang.Properties.Completeness
module Completeness (A : Domain) where
  open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; inject₁)
  open import Data.Multiset (VariantSetoid ∞ A) as Iso using (_∈_; _⊆_)

  encode : (n : ℕ) → VSet A n → VariantList ∞ A
  encode    zero vs = vs zero ∷ []
  encode (suc n) vs = encode n (forget-last vs) ⁺∷ʳ vs (fromℕ (suc n))

  encode-⊆-n-zero :
    ∀ (n : ℕ)
    → (m : Fin (suc n))
    → (vs : VSet A n)
    → ⟦ encode n vs ⟧ ⊆ vs
    → ⟦ encode n vs ⟧ (toℕ m) ≡ vs m

  flubi :
    ∀ (n : ℕ)
    → (vs : VSet A (suc n))
    → encode (suc n) vs ≡ encode n (forget-last vs)
  flubi = {!!}

  encode-⊆ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → ⟦ encode n vs ⟧ ⊆ vs
  encode-⊆    zero vs    i    = zero , must-take-whats-left i
  encode-⊆ (suc n) vs    zero with encode n (forget-last vs)
  ... | e ∷ es = zero , (
      ⟦ (e ∷ es) ⁺∷ʳ vs (suc (fromℕ n)) ⟧ zero
    ≡⟨⟩
      ⟦ e ∷ (es Data.List.∷ʳ vs (suc (fromℕ n))) ⟧ zero
    ≡⟨⟩
      find (e ∷ (es Data.List.∷ʳ vs (suc (fromℕ n)))) zero
    ≡⟨⟩
      e
      -- find (encode n (forget-last vs) ⁺∷ʳ vs (suc (fromℕ n))) zero
    -- ≡⟨⟩
      -- find (encode n (forget-last vs) ⁺∷ʳ vs (suc (fromℕ n))) zero
    ≡⟨ {!!} ⟩
      find (encode zero (forget-all vs)) zero
    ≡⟨ {!!} ⟩ -- use flubi here
      vs zero
    ∎) --encode-⊆-n-zero n zero (forget-last vs) (encode-⊆ n (forget-last vs))
  encode-⊆ (suc n) vs (suc i) = {!!}
  -- encode-⊆ (suc n) vs (suc i) with encode n (forget-last vs) | encode-⊆-n-zero n (clamp (suc n) i) (forget-last vs) (encode-⊆ n (forget-last vs))
  -- ... | e ∷ es | foo =
  --   let subindex = clamp (suc n) (suc i)
  --       index = suc subindex
  --       tail = vs (fromℕ (suc n))
  --    in index , (
  --         ⟦ (e ∷ es) ⁺∷ʳ tail ⟧ (suc i)
  --       ≡⟨⟩
  --         ⟦ toList (e ∷ es) ∷ʳ tail ⟧ (suc i)
  --       ≡⟨⟩
  --         ⟦ e ∷ (es Data.List.∷ʳ tail) ⟧ (suc i)
  --       ≡⟨⟩
  --         lookup-clamped (suc i) (e ∷ (es Data.List.∷ʳ tail))
  --       ≡⟨ {!!} ⟩
  --         lookup-clamped i (es ∷ʳ tail)
  --       ≡⟨⟩
  --         ⟦ es ∷ʳ tail ⟧ i
  --       ≡⟨ {!!} ⟩
  --         vs index
  --       ∎)

  encode-⊆-n-zero zero zero _ _ = refl
  encode-⊆-n-zero (suc n) zero vs x with encode (suc n) vs | x zero
  ... | head ∷ tail | zero , snd = snd
  ... | head ∷ tail | suc i , snd = {!!}
  encode-⊆-n-zero (suc n) (suc m) vs x = {!!} -- encode-⊆-n-zero n m (forget-last vs) ?
  -- encode-⊆-n-zero zero zvs x = ?
  -- encode-⊆-n-zero (suc n) vs x with x zero
  -- ... |  zero , snd  = snd
  -- ... | suc m , snd = -- suc m , lookup-clamped (suc m) (encode n vs) ∈ vs
  --   encode-⊆-n-zero n (forget-last vs) snd
  --   -- begin
  --   --   ⟦ encode n (forget-last vs) ⟧ zero
  --   -- ≡⟨ ? ⟩
  --   --   vs zero
  --   -- ∎


  encode-⊇ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → vs ⊆ ⟦ encode n vs ⟧
  encode-⊇ zero vs zero = zero , refl
  encode-⊇ (suc n) vs i = {!!}

VariantList-is-complete : Complete VariantListL
VariantList-is-complete {A} {n} vs =
  let open Completeness A
   in (record { get = encode n vs }) , encode-⊇ n vs , encode-⊆ n vs
```



