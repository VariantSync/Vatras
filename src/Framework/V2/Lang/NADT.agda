{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
-- TODO: Generalize level of F
module Framework.V2.Lang.NADT (F : 𝔽) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  Choice = VLChoiceₙ.Syntax
  Config = Choiceₙ.Config
  choice-semantics = VLChoiceₙ.Semantics

data NADT : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf A              → NADT i A
  NADTChoice : ∀ {i A} → Choice F (NADT i) A → NADT (↑ i) A

mutual
  NADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant F Config
  NADTVL {i} = syn NADT i with-sem semantics

  semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant F Config (NADT i)
  semantics (NADTAsset a) _  = VLLeaf.elim-leaf F VLLeaf.Leaf∈ₛGrulerVariant a
  semantics (NADTChoice chc) = choice-semantics GrulerVariant F id NADTVL chc
