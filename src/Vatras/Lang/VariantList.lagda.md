# Clone-and-Own as a Variability Language

The simples way to express variability is to just list all the alternatives.
In software engineering, developing software like this is know as _clone-and-own_.
Formally, expressing variability in this way amounts to declaring a list of variants.

## Module

```agda
open import Vatras.Framework.Definitions using (𝕍; 𝔼; ℂ)
module Vatras.Lang.VariantList (V : 𝕍) where
```

## Imports

```agda
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ)

open import Vatras.Framework.VariabilityLanguage using (𝔼-Semantics; VariabilityLanguage; ⟪_,_,_⟫)
open import Vatras.Util.List using (find-or-last)
```

## Syntax

```agda
VariantList : 𝔼
VariantList A = List⁺ (V A)

{-|
Just an alias.
-}
Clone-and-Own : 𝔼
Clone-and-Own = VariantList
```

## Semantics

```agda
{-|
To obtain a variant, we have to do a list lookup.
Hence, a configuration is just an index / address in that list.
For simplicity, we allow just any natural number and just pick the
last variant in case of an overview.
Otherwise, the type of configuration must be parameterized in the
particular expression to configure.
-}
Configuration : ℂ
Configuration = ℕ

{-|
Semantics is just a list lookup.
-}
-- ⟦_⟧ : ∀ {i : Size} {A : 𝔸} → VariantList i A → Configuration → Variant i A
⟦_⟧ : 𝔼-Semantics V Configuration VariantList
⟦ clones ⟧ i = find-or-last i clones
```

## Clone-and-Own as a Variability Language

```agda
VariantListL : VariabilityLanguage V
VariantListL = ⟪ VariantList , Configuration , ⟦_⟧ ⟫
```
