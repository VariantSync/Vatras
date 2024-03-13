# Fixed Arity Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

It's required that arity is at least one to have a semantic. However, we require
that the arity is at least two, otherwise there is this annoying one-arity
language in the NCC language family which is incomplete.

```agda
open import Framework.Definitions
open import Util.Nat.AtLeast using (ℕ≥)
module Lang.NCC (n : ℕ≥ 2) (Dimension : 𝔽) where
```

## Imports

```agda
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.Variants
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
open import Construct.Choices
```

## Syntax

```agda
data NCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (NCC i) A → NCC (↑ i) A
   chc  : ∀ {i A} → VLNChoice.Syntax n Dimension (NCC i) A → NCC (↑ i) A

pattern _-<_>- a cs = atom (a At.-< cs >-)
pattern _⟨_⟩ D cs = chc (D NChoice.⟨ cs ⟩)
```

## Semantics

```agda
Configuration : 𝕂
Configuration = NChoice.Config n Dimension

module Sem (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    NCCL : ∀ {i : Size} → VariabilityLanguage V
    NCCL {i} = ⟪ NCC i , Configuration , ⟦_⟧ ⟫

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V Configuration (NCC i)
    ⟦ atom x ⟧ = PlainConstruct-Semantics Artifact-Construct mkArtifact NCCL x
    ⟦ chc  x ⟧ = VLNChoice.Semantics n V Dimension NCCL id x
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)
import Data.Vec as Vec

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → NCC i A → List Dimension
dims (_ -< es >-) = concatMap dims es
dims (D ⟨ cs ⟩) = D ∷ concatMap dims (Vec.toList cs)
```

## Show

```agda
open import Data.String using (String; _++_; intersperse)
module Pretty (show-D : Dimension → String) where
  open import Show.Lines

  show : ∀ {i} → NCC i String → String
  show (a -< [] >-) = a
  show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
  show (D ⟨ cs ⟩) = show-D D ++ "⟨" ++ (intersperse ", " (mapl show (Vec.toList cs))) ++ "⟩"


  pretty : ∀ {i : Size} → NCC i String → Lines
  pretty (a -< [] >-) = > a
  pretty (a -< es@(_ ∷ _) >-) = do
    > a ++ "-<"
    indent 2 do
      lines (mapl pretty es)
    > ">-"
  pretty (D ⟨ cs ⟩) = do
    > show-D D ++ "⟨"
    indent 2 do
      lines (mapl pretty (Vec.toList cs))
    > "⟩"
```
