{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.BCC (F : Set) where

open import Data.Bool using (Bool)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Variants
open import Framework.V2.Constructs.Artifact using () renaming (Syntax to Artifact; Semantics to at-sem)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (Config)
open Chc.VLChoice₂ F using () renaming (Syntax to Choice₂; Semantics to chc-sem)

data BCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (BCC i) A → BCC (↑ i) A
   chc  : ∀ {i A} → Choice₂  (BCC i) A → BCC (↑ i) A

module _ (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    BCCL : ∀ {i : Size} → VariabilityLanguage V (Config F)
    BCCL {i} = syn BCC i with-sem ⟦_⟧

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V (Config F) (BCC i)
    ⟦ atom x ⟧ = at-sem (Config F) mkArtifact id BCCL x
    ⟦ chc  x ⟧ = chc-sem V id BCCL x
