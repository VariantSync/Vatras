{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
-- TODO: Generalize level of F
module Framework.V2.Lang.2ADT (F : 𝔽) where

open import Data.Bool using (Bool)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.VariabilityLanguage
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Constructs.NestedChoice F public
open import Framework.V2.Variants using (GrulerVariant)

private
  Choice₂ = VLChoice₂.Syntax
  Config₂ = Choice₂.Config

2ADT : Size → 𝔼
2ADT i A = NestedChoice i (Leaf A)

mutual
  2ADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
  2ADTVL {i} = Lang-⟪ 2ADT i , Config₂ F , semantics ⟫

  semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant (Config₂ F) (2ADT i)
  semantics e c = VLLeaf.elim-leaf VLLeaf.Leaf∈ₛGrulerVariant (⟦ e ⟧ c)
