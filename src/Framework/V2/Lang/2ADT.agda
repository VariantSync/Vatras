{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
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

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant F Bool (2ADT i)

2ADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant F Bool
2ADTVL {i} = syn 2ADT i with-sem semantics

semantics (2ADTAsset a) _  = VLLeaf.elim-leaf F VLLeaf.Leaf∈ₛGrulerVariant a
semantics (2ADTChoice chc) = choice₂-semantics GrulerVariant F id 2ADTVL chc
