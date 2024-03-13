{-# OPTIONS --sized-types #-}

open import Framework.Definitions
-- TODO: Generalize level of F
module Lang.2ADT (F : 𝔽) where

open import Data.Bool using (Bool)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Construct.GrulerArtifacts
open import Construct.Choices
open import Construct.NestedChoice F as NestedChoice using (NestedChoice)

2ADT : Size → 𝔼
2ADT i A = NestedChoice i (Leaf A)

mutual
  2ADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
  2ADTVL {i} = ⟪ 2ADT i , 2Choice.Config F , semantics ⟫

  semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant (2Choice.Config F) (2ADT i)
  semantics e c = VLLeaf.elim-leaf VLLeaf.Leaf∈ₛGrulerVariant (NestedChoice.⟦ e ⟧ c)
