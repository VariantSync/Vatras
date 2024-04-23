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

data NADT (F : 𝔽) : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf (Variant A)               → NADT F (↑ i) A
  NADTChoice : ∀ {i A} → VLChoice.Syntax F (NADT F i) A → NADT F (↑ i) A

mutual
  NADTL : ∀ {i : Size} (F : 𝔽) → VariabilityLanguage
  NADTL {i} F = ⟪ NADT F i , Choice.Config F , ⟦_⟧ ⟫

  ⟦_⟧ : ∀ {i : Size} {F : 𝔽} → 𝔼-Semantics (Choice.Config F) (NADT F i)
  ⟦_⟧ (NADTAsset (leaf v)) _   = v
  ⟦_⟧ {i} {F} (NADTChoice chc) = VLChoice.Semantics F (NADTL F) id chc
