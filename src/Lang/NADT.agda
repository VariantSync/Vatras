{-# OPTIONS --sized-types #-}

open import Framework.Definitions
-- TODO: Generalize level of F
module Lang.NADT (F : 𝔽) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts
open import Construct.Choices

private
  Choiceₙ = VLChoiceₙ.Syntax
  Configₙ = Choiceₙ.Config
  choice-semantics = VLChoiceₙ.Semantics

data NADT : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf A              → NADT i A
  NADTChoice : ∀ {i A} → Choiceₙ F (NADT i) A → NADT (↑ i) A

mutual
  NADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
  NADTVL {i} = ⟪ NADT i , Configₙ F , semantics ⟫

  semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant (Configₙ F) (NADT i)
  semantics (NADTAsset a) _  = VLLeaf.elim-leaf VLLeaf.Leaf∈ₛGrulerVariant a
  semantics (NADTChoice chc) = choice-semantics GrulerVariant F NADTVL id chc
