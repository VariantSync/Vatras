{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Lang.NADT where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.Construct
open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts
open import Construct.Choices

data NADT (V : 𝕍) (F : 𝔽) : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf (V A)                       → NADT V F (↑ i) A
  NADTChoice : ∀ {i A} → VLChoice.Syntax F (NADT V F i) A → NADT V F (↑ i) A

mutual
  NADTL : ∀ {i : Size} (V : 𝕍) (F : 𝔽) → VariabilityLanguage V
  NADTL {i} V F = ⟪ NADT V F i , Choice.Config F , ⟦_⟧ ⟫

  ⟦_⟧ : ∀ {i : Size} {V : 𝕍} {F : 𝔽} → 𝔼-Semantics V (Choice.Config F) (NADT V F i)
  ⟦_⟧ (NADTAsset (leaf v)) _   = v
  ⟦_⟧ {i} {V} {F} (NADTChoice chc) = VLChoice.Semantics V F (NADTL V F) id chc
