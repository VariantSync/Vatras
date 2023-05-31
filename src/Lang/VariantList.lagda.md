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
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.NonEmpty using (List⁺; _∷_; toList; length; _⁺∷ʳ_; _∷ʳ_)
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

find-cong-r : ∀ {A : Set}
  → (x : A)
  → (l : List⁺ A)
  → (i : ℕ)
  → (suc i < length (l ⁺∷ʳ x))
  → find (l ⁺∷ʳ x) i ≡ find l i
find-cong-r x (head ∷ tail) zero x₁ = refl
find-cong-r x (head ∷ []) (suc i) (s≤s (s≤s ()))
find-cong-r x (head ∷ y ∷ ys) (suc i) (s≤s (s≤s suci≤len[y++x])) =
    find (y ∷ ys ++ [ x ]) i
  ≡⟨ {!!} ⟩
    find (y ∷ ys) i
  ∎
  -- let i = zero in
    -- find (y ∷ ys)  ⁺∷ʳ x) (suc i)
  -- ≡⟨⟩
  --   find (toList (head ∷ []) ∷ʳ x) (suc i)
  -- ≡⟨⟩
  --   find (head ∷ toList ([] ∷ʳ x)) (suc i)
  -- ≡⟨⟩
  --   find (head ∷ toList (x ∷ [])) (suc i)
  -- ≡⟨⟩
  --   find (head ∷ x ∷ []) (suc i)
  -- ≡⟨ {!!} ⟩
  --   find (head ∷ []) (suc i)
  -- ∎
  --   find (l ⁺∷ʳ x) (suc i)
  -- ≡⟨ find-cong-r {!!} ⟩
  --   find l (suc i)
  -- ∎

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
  open Data.Nat using (_∸_)
  open Data.Product using (proj₁; proj₂)
  open import Data.Nat.Properties using (m∸n≤m; m<n⇒m<1+n)
  open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; fromℕ<; inject₁)
  open import Data.Multiset (VariantSetoid ∞ A) as Iso using (_∈_; _⊆_)

  encode : (n : ℕ) → VSet A n → VariantList ∞ A
  encode    zero vs = vs zero ∷ []
  encode (suc n) vs = vs (fromℕ (suc n)) ∷ toList (encode n (forget-last vs)) -- ⁺∷ʳ vs (fromℕ (suc n))

  -- encode-⊆-n-zero :
  --   ∀ (n : ℕ)
  --   → (m : Fin (suc n))
  --   → (vs : VSet A n)
  --   → ⟦ encode n vs ⟧ ⊆ vs
  --   → ⟦ encode n vs ⟧ (toℕ m) ≡ vs m

  -- flubi :
  --   ∀ (n : ℕ)
  --   → (m : ℕ)
  --   → (m ≤ n)
  --   → (vs : VSet A (suc n))
  --   → ⟦ encode (suc n) vs ⟧ m ≡ ⟦ encode n (forget-last vs) ⟧ m
  -- flubi zero    zero x vs = refl
  -- flubi (suc n) zero x vs = refl
  -- flubi (suc n) (suc m) (s≤s m≤n) vs =
  --     ⟦ encode (suc (suc n)) vs ⟧ (suc m)
  --   ≡⟨⟩
  --     ⟦ encode (suc n) (forget-last vs) ⁺∷ʳ vs (fromℕ (suc (suc n))) ⟧ (suc m)
  --   ≡⟨ find-cong-r
  --        (vs (fromℕ (suc (suc n))))
  --        (encode (suc n) (forget-last vs))
  --        (suc m)
  --        (s≤s {!!})
  --        ⟩
  --     ⟦ encode (suc n) (forget-last vs) ⟧ (suc m)
  --   ∎
  --   where hypot : ⟦ encode (suc n) (forget-last vs) ⟧ m ≡ ⟦ encode n (forget-last (forget-last vs)) ⟧ m
  --         hypot = flubi n m m≤n (forget-last vs)

  -- m<n⇒1+m<1+n ∀ {m n : ℕ} → m < n → suc m < suc n
  -- m

  encode-⊆ :
    ∀ (n : ℕ)
    → (vs : VSet A n)
    → ⟦ encode n vs ⟧ ⊆ vs
  encode-⊆   zero  vs      i  = zero , must-take-whats-left i
  encode-⊆ (suc n) vs   zero  = fromℕ (suc n) , refl
  encode-⊆ (suc n) vs (suc i) =
    let config-ℕ : ℕ
        config-ℕ = suc n ∸ suc i

        le1 : config-ℕ < suc n
        le1 = s≤s (m∸n≤m n i)

        le2 : (n ∸ i) < suc (suc n)
        le2 = m<n⇒m<1+n le1

        config-Fin : Fin (suc (suc n))
        config-Fin = fromℕ< le2

        hypot : ⟦ encode n (forget-last vs) ⟧ ⊆ forget-last vs
        hypot = encode-⊆ n (forget-last vs)

        hypot2 : ⟦ encode n (forget-last vs) ⟧ i ∈ forget-last vs
        hypot2 = encode-⊆ n (forget-last vs) i

        j : Fin (suc n)
        j = proj₁ hypot2
    in
    config-Fin , (
      ⟦ vs (suc (fromℕ n)) ∷ toList (encode n (forget-last vs)) ⟧ (suc i)
    ≡⟨⟩
      ⟦ encode n (forget-last vs) ⟧ i
    ≡⟨ proj₂ hypot2 ⟩
      (forget-last vs) j -- Wait. Maybe just use j here as config???
    ≡⟨ {!!} ⟩
      vs config-Fin
    ∎)

    -- (
    --   ⟦ encode (suc n) vs ⟧ zero
    -- ≡⟨ flubi n zero {!!} vs ⟩
    --   ⟦ encode n (forget-last vs) ⟧ zero
    -- ≡⟨ hypot ⟩
    --   vs zero
    -- ∎)
    -- where foo = encode-⊆ n (forget-last vs) zero
    --       hypot : ⟦ encode n (forget-last vs) ⟧ zero ≡ vs zero
    --       hypot = {!!}
  -- encode-⊆ (suc n) vs (suc i) = {!!}
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

  -- encode-⊆-n-zero zero zero _ _ = refl
  -- encode-⊆-n-zero (suc n) zero vs x with encode (suc n) vs | x zero
  -- ... | head ∷ tail | zero , snd = snd
  -- ... | head ∷ tail | suc i , snd = {!!}
  -- encode-⊆-n-zero (suc n) (suc m) vs x = {!!} -- encode-⊆-n-zero n m (forget-last vs) ?
  -- -- encode-⊆-n-zero zero zvs x = ?
  -- -- encode-⊆-n-zero (suc n) vs x with x zero
  -- -- ... |  zero , snd  = snd
  -- -- ... | suc m , snd = -- suc m , lookup-clamped (suc m) (encode n vs) ∈ vs
  -- --   encode-⊆-n-zero n (forget-last vs) snd
  -- --   -- begin
  -- --   --   ⟦ encode n (forget-last vs) ⟧ zero
  -- --   -- ≡⟨ ? ⟩
  -- --   --   vs zero
  -- --   -- ∎


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



