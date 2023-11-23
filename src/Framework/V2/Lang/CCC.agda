{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.CCC (F : 𝔽) where

open import Function using (id)
open import Size using (Size; ↑_; ∞)

open import Framework.V2.Variants
open import Framework.V2.VariabilityLanguage
open import Framework.V2.Construct
open import Framework.V2.Constructs.Artifact using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
import Framework.V2.Constructs.Choices as Chc
open Chc.VLChoiceₙ using () renaming (Syntax to Choiceₙ; Semantics to chc-sem)
open Chc.Choiceₙ using () renaming (Config to Configₙ)

data CCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact  (CCC i) A → CCC (↑ i) A
   chc  : ∀ {i A} → Choiceₙ F (CCC i) A → CCC (↑ i) A

module _ (V : 𝕍) (mkArtifact : Artifact ∈ₛ V) where
  mutual
    CCCL : ∀ {i : Size} → VariabilityLanguage V
    CCCL {i} = Lang-⟪ CCC i , Configₙ F , ⟦_⟧ ⟫

    ⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V (Configₙ F) (CCC i)
    ⟦ atom x ⟧ = PlainConstruct-Semantics Artifact-Construct mkArtifact CCCL x
    ⟦ chc  x ⟧ = chc-sem V F CCCL id x
