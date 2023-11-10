{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
-- TODO: Generalize level of F
module Framework.V2.Lang.2ADT (F : 𝔽) where

open import Data.Bool using (Bool)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  Choice₂ = VLChoice₂.Syntax
  choice₂-semantics = VLChoice₂.Semantics

data 2ADT : Size → 𝔼 where
  2ADTAsset  : ∀ {i A} → Leaf A → 2ADT i A
  2ADTChoice : ∀ {i A} → Choice₂ F (2ADT i) A → 2ADT (↑ i) A

mutual
  2ADTVL : ∀ {i : Size} → (R : (F → Bool) → Set) → VariabilityLanguage GrulerVariant F Bool R
  2ADTVL {i} R = syn 2ADT i with-sem semantics R

  semantics : ∀ {i : Size} → (R : (F → Bool) → Set) → 𝔼-Semantics GrulerVariant F Bool R (2ADT i)
  semantics R (2ADTAsset a) _  = VLLeaf.elim-leaf F VLLeaf.Leaf∈ₛGrulerVariant a
  semantics R (2ADTChoice chc) = choice₂-semantics GrulerVariant F R id (2ADTVL R) chc
