{-# OPTIONS --allow-unsolved-metas #-}

open import Framework.V2.Definitions
module Framework.V2.Translation.NChoice-to-2Choice-Test (F : 𝔽) where

open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Framework.V2.Compiler using (ConstructCompiler)
open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)
open Chc.VLChoice₂ using () renaming (Construct to C₂)
open Chc.VLChoiceₙ using () renaming (Construct to Cₙ)
open import Framework.V2.Translation.NChoice-to-2Choice {Q = F} as BLUB
open BLUB.Translate ℕ

example : ∀ {D : F} → D ⟨ 1 , 2 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , val 2 ⟩) ⟩
example = step base

example' : ∀ {D : F}
  → D ⟨ 1 , 2 ∷ 3 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , chc ((D ∙ 2) ⟨ val 3 , val 3 ⟩) ⟩) ⟩
example' = step (step base)
