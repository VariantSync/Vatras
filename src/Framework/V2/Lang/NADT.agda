{-# OPTIONS --sized-types #-}
module Framework.V2.Lang.NADT where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Definitions
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  Choice = VLChoiceₙ.Syntax
  Choice-Semantics = VLChoiceₙ.Semantics

data NADT : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → Leaf A              → NADT i A
  NADTChoice : ∀ {i A} → Choice ℕ (NADT i) A → NADT (↑ i) A

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant ℕ ℕ (NADT i)

NADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant ℕ ℕ
NADTVL {i} = syn NADT i with-sem semantics

semantics (NADTAsset a) _  = VLLeaf.elim-leaf ℕ VLLeaf.Leaf∈ₛGrulerVariant a
semantics (NADTChoice chc) = Choice-Semantics GrulerVariant ℕ id NADTVL chc
