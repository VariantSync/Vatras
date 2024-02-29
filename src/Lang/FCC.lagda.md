# Fixed Arity Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Framework.Definitions
open import Util.Nat.AtLeast using (ℕ≥)
module Lang.FCC (n : ℕ≥ 2) (Dimension : 𝔽) where
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
import Construct.Choices as Chc
open Chc.VLChoice-Fix using () renaming (Syntax to Choice-Fix; Semantics to chc-sem)
open Chc.Choice-Fix using () renaming (Config to Config-Fix)
```

## Syntax

```agda
data FCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (FCC i) A → FCC (↑ i) A
   chc  : ∀ {i A} → Choice-Fix n Dimension (FCC i) A → FCC (↑ i) A

pattern _-<_>- a cs  = atom (a At.-< cs >-)
pattern _⟨_⟩ D cs = chc  (D Chc.Choice-Fix.⟨ cs ⟩)
```

## Semantics

```agda
Configuration : 𝕂
Configuration = Config-Fix n Dimension

module Sem (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    FCCL : ∀ {i : Size} → VariabilityLanguage V
    FCCL {i} = ⟪ FCC i , Configuration , ⟦_⟧ ⟫

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V Configuration (FCC i)
    ⟦ atom x ⟧ = PlainConstruct-Semantics Artifact-Construct mkArtifact FCCL x
    ⟦ chc  x ⟧ = chc-sem n V Dimension FCCL id x
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)
import Data.Vec as Vec

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → FCC i A → List Dimension
dims (_ -< es >-) = concatMap dims es
dims (D ⟨ cs ⟩) = D ∷ concatMap dims (Vec.toList cs)
```

## Show

```agda
open import Data.String using (String; _++_; intersperse)
module Pretty (show-D : Dimension → String) where
  open import Show.Lines

  show : ∀ {i} → FCC i String → String
  show (a -< [] >-) = a
  show (a -< es@(_ ∷ _) >-) = a ++ "-<" ++ (intersperse ", " (mapl show es)) ++ ">-"
  show (D ⟨ cs ⟩) = show-D D ++ "⟨" ++ (intersperse ", " (mapl show (Vec.toList cs))) ++ "⟩"


  pretty : ∀ {i : Size} → FCC i String → Lines
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
