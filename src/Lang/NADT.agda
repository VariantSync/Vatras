{-# OPTIONS --sized-types #-}

open import Framework.Definitions
-- TODO: Generalize level of F
module Lang.NADT (F : 𝔽) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.Construct
open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts
open import Construct.Choices

data NADT : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf A                       → NADT i A
  NADTChoice : ∀ {i A} → VLChoice.Syntax F (NADT i) A → NADT (↑ i) A

mutual
  NADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
  NADTVL {i} = ⟪ NADT i , Choice.Config F , semantics ⟫

  semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant (Choice.Config F) (NADT i)
  semantics (NADTAsset a) _  = VLLeaf.elim-leaf VLLeaf.Leaf∈ₛGrulerVariant a
  semantics (NADTChoice chc) = VLChoice.Semantics GrulerVariant F NADTVL id chc
