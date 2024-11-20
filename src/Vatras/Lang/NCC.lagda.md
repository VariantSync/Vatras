# Fixed Arity Choice Calculus

This module defines the choice calculus in which every choice must have the same
fixed number of alternatives, called $n-CC$ in our paper.

It's required that arity $n$ is at least one to have semantics. However, we require
that the arity is at least two, otherwise there is this annoying one-arity
language in the NCC language family which is incomplete.
In our paper, we also only inspect the languages with `n ≥ 2`.

## Module

```agda
open import Vatras.Framework.Definitions
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥)
module Vatras.Lang.NCC (Dimension : 𝔽) (n : ℕ≥ 2) where
```

## Imports

```agda
open import Data.Fin using (Fin)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage using (𝔼-Semantics; VariabilityLanguage; ⟪_,_,_⟫)
```

## Syntax

```agda
data NCC : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (NCC i A) → NCC (↑ i) A
   _⟨_⟩ : ∀ {i A} → Dimension → Vec (NCC i A) (ℕ≥.toℕ n) → NCC (↑ i) A
```

## Semantics

The semantics is very similar to the semantics for core choice calculus.
The differences are:

- We can restrict configuration to choose alternatives within bounds because the arity of choices is known in advance.
- We can then do a vector lookup instead of a list lookup in the semantics.

```agda
Configuration : ℂ
Configuration = Dimension → Fin (ℕ≥.toℕ n)

⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics (Rose ∞) Configuration (NCC i)
⟦ a -< cs >- ⟧ c = a V.-< List.map (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ cs ⟩   ⟧ c = ⟦ Vec.lookup cs (c D) ⟧ c

{-|
NCC is a variability language for all n ≥ 2.
-}
NCCL : ∀ {i : Size} → VariabilityLanguage (Rose ∞)
NCCL {i} = ⟪ NCC i , Configuration , ⟦_⟧ ⟫
```
