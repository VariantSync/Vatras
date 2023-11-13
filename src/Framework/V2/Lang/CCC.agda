{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.CCC (F : 𝔽) where

open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.V2.Variants
open import Framework.V2.Constructs.Artifact using () renaming (Syntax to Artifact; Semantics to at-sem)
import Framework.V2.Constructs.Choices as Chc
open Chc.VLChoiceₙ using () renaming (Syntax to Choiceₙ; Semantics to chc-sem)

data CCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact A (CCC i) A → CCC (↑ i) A
   chc  : ∀ {i A} → Choiceₙ  F (CCC i) A → CCC (↑ i) A

module _ (V : 𝕍) (mkArtifact : F ⊢ Artifact ∈ₛ V) where
  mutual
    CCCL : ∀ {i : Size} → VariabilityLanguage V F ℕ
    CCCL {i} = syn CCC i with-sem ⟦_⟧

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V F ℕ (CCC i)
    ⟦ atom x ⟧ = at-sem F ℕ mkArtifact id CCCL x
    ⟦ chc  x ⟧ = chc-sem V F id CCCL x
