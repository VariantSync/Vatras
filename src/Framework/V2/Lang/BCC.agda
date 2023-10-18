{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Lang.BCC (F : 𝔽) where

open import Size using (Size; ↑_)

open import Framework.V2.Constructs.Artifact
import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using () renaming (Syntax to Choice₂)

data BCC : Size → 𝔼 where
   atom : ∀ {i A} → Artifact A (BCC i A) → BCC (↑ i) A
   chc  : ∀ {i A} → Choice₂ F (BCC i A) → BCC (↑ i) A
