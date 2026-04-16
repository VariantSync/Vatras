# Fixed Arity Choice Calculus

This module defines the choice calculus in which every choice must have the same
fixed number of alternatives, called $n-CC$ in our paper.

We require the arity $n$ to be at least two.
An arity of zero would mean that all choices have zero alternatives.
Choices with zero alternatives hence would constitute leaf terms without a clear purpose.
Choices with exactly one alternative have only one way to be configured: selecting that single alternative.
In both cases of an arity of zero or one, an $n-CC$ term denotes a single constant variant.
For this reason, we restrict $n$ to be at least two, as we also did in our paper.

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
The only difference is that we can restrict the configuration process to choose alternatives within bounds because the arity of choices is known in advance.
We hence do a vector lookup instead of a list lookup.

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
