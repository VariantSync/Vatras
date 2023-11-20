{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.BCC (F : 𝔽) where

open import Data.Bool using (Bool)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Variants
open import Framework.V2.Constructs.Artifact using () renaming (Syntax to Artifact; Semantics to at-sem)
import Framework.V2.Constructs.Choices as Chc
open Chc.VLChoice₂ using () renaming (Syntax to Choice₂; Semantics to chc-sem)
open Chc.Choice₂ using () renaming (Config to Config₂)

data BCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (BCC i) A → BCC (↑ i) A
   chc  : ∀ {i A} → Choice₂  F (BCC i) A → BCC (↑ i) A

module _ (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    BCCL : ∀ {i : Size} → VariabilityLanguage V (Config₂ F)
    BCCL {i} = syn BCC i with-sem ⟦_⟧

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V (Config₂ F) (BCC i)
    ⟦ atom x ⟧ = at-sem (Config₂ F) mkArtifact id BCCL x
    ⟦ chc  x ⟧ = chc-sem V F id BCCL x
