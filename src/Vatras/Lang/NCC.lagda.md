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
module Vatras.Lang.NCC (n : ℕ≥ 2) (Dimension : 𝔽) where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.Vec as Vec using (Vec)
open import Data.Product using (_,_)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage
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
⟦ a -< cs >- ⟧ c = a V.-< mapl (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ cs ⟩   ⟧ c = ⟦ Vec.lookup cs (c D) ⟧ c

{-|
NCC is a variability language for all n ≥ 2.
-}
NCCL : ∀ {i : Size} → VariabilityLanguage (Rose ∞)
NCCL {i} = ⟪ NCC i , Configuration , ⟦_⟧ ⟫
```

## Utility

Recursively, collect all dimensions used in an n-CC expression:
```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)
import Data.Vec as Vec

dims : ∀ {i : Size} {A : 𝔸} → NCC i A → List Dimension
dims (_ -< es >-) = concatMap dims es
dims (D ⟨ cs ⟩) = D ∷ concatMap dims (Vec.toList cs)
```

## Show

```agda
open import Data.String as String using (String; _++_; intersperse)
module Pretty (show-D : Dimension → String) where
  open import Vatras.Show.Lines

  show : ∀ {i} → NCC i (String , String._≟_) → String
  show (a -< [] >-) = a
  show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
  show (D ⟨ cs ⟩) = show-D D ++ "⟨" ++ (intersperse ", " (mapl show (Vec.toList cs))) ++ "⟩"


  pretty : ∀ {i : Size} → NCC i (String , String._≟_) → Lines
  pretty (a -< [] >-) = > a
  pretty (a -< es@(_ ∷ _) >-) = do
    > a ++ "-<"
    indent 2 do
      intersperseCommas (mapl pretty es)
    > ">-"
  pretty (D ⟨ cs ⟩) = do
    > show-D D ++ "⟨"
    indent 2 do
      intersperseCommas (mapl pretty (Vec.toList cs))
    > "⟩"
```
