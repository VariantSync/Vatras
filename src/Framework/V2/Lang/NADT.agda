module Framework.V2.Lang.NADT where

open import Data.Nat using (ℕ)
open import Function using (id)

open import Framework.V2.Definitions
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  variable
    A : 𝔸

  Choice = VLChoiceₙ.Syntax
  Choice-Semantics = VLChoiceₙ.Semantics

data NADT : 𝔼 where
  NADTAsset  : Leaf A          → NADT A
  NADTChoice : Choice ℕ NADT A → NADT A

{-# TERMINATING #-}
⟦_⟧-nadt : 𝔼-Semantics GrulerVariant ℕ ℕ NADT

NADTVL : VariabilityLanguage GrulerVariant ℕ ℕ
Expression NADTVL = NADT
Semantics  NADTVL = ⟦_⟧-nadt

⟦ NADTAsset A  ⟧-nadt = VLLeaf.Semantics VLLeaf.Leaf∈ₛGrulerVariant id NADTVL A
⟦ NADTChoice C ⟧-nadt = Choice-Semantics GrulerVariant ℕ id NADTVL C
