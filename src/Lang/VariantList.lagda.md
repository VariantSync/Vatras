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
open import Data.List using (_∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
open import Size using (Size; ∞)

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

-- ⟦_⟧ : ∀ {i : Size} {A : Domain} → VariantList i A → Configuration → Variant i A
⟦_⟧ : Semantics VariantList Configuration
⟦ vs ⟧ i = lookup-clamped i vs

VariantListL : VariabilityLanguage
VariantListL = record
  { expression    = VariantList
  ; configuration = Configuration
  ; semantics     = ⟦_⟧
  }
```

## Properties

```agda
open import Data.Product
open import Data.Fin
open import Lang.Properties.Completeness

encode : ∀ {A} → (n : ℕ) → VSet A n → VariantList ∞ A
encode    zero vs = vs zero ∷ []
encode (suc n) vs = vs (fromℕ (suc n)) ∷ toList (encode n (forget-last vs))

VariantList-is-complete : Complete VariantListL
VariantList-is-complete {A} {n} vs =
  let e : VariantList ∞ A
      e = encode n vs
  in (record { get = e }) , ((λ i → toℕ i , {!!}) , λ i → {!!} , {!!})
```



