{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.CCC (F : Set) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.V2.Variants
open import Framework.V2.Constructs.Artifact using () renaming (Syntax to Artifact; Semantics to at-sem)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choiceₙ using (Config)
open Chc.VLChoiceₙ F using () renaming (Syntax to Choiceₙ; Semantics to chc-sem)

data CCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact (CCC i) A → CCC (↑ i) A
   chc  : ∀ {i A} → Choiceₙ  (CCC i) A → CCC (↑ i) A

module _ (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    CCCL : ∀ {i : Size} → VariabilityLanguage V (Config F)
    CCCL {i} = syn CCC i with-sem ⟦_⟧

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V (Config F) (CCC i)
    ⟦ atom x ⟧ = at-sem (Config F) mkArtifact id CCCL x
    ⟦ chc  x ⟧ = chc-sem V id CCCL x
