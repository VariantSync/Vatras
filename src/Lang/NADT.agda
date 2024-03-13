{-# OPTIONS --sized-types #-}

open import Framework.Definitions
-- TODO: Generalize level of F
module Lang.NADT (F : 𝔽) (V : 𝕍) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.Construct
open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts
open import Construct.Choices

data NADT : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf (V A)                   → NADT i A
  NADTChoice : ∀ {i A} → VLChoice.Syntax F (NADT i) A → NADT (↑ i) A

mutual
  NADTVL : ∀ {i : Size} → VariabilityLanguage V
  NADTVL {i} = ⟪ NADT i , Choice.Config F , semantics ⟫

  semantics : ∀ {i : Size} → 𝔼-Semantics V (Choice.Config F) (NADT i)
  semantics (NADTAsset (leaf v)) _ = v
  semantics (NADTChoice chc)       = VLChoice.Semantics V F NADTVL id chc
