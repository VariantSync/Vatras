{-|
This module defines algebraic decision trees as defined in our paper.
-}
open import Vatras.Framework.Definitions
module Vatras.Lang.ADT (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (Bool; if_then_else_)
open import Vatras.Framework.VariabilityLanguage

{-|
An algebraic decision tree stores variants in leaf nodes
and decorates them with binary choices.
-}
data ADT : 𝔼 where
  leaf   : ∀ {A} → V A → ADT A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : ADT A) → (r : ADT A) → ADT A

Configuration : ℂ
Configuration = F → Bool

{-|
To configure an ADT, we basically walk down from the root to the
leaf node holding the desired variant.
We do this by evaluating each choice until we hit a leaf.
-}
⟦_⟧ : 𝔼-Semantics V Configuration ADT
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

ADTL : VariabilityLanguage V
ADTL = ⟪ ADT , Configuration , ⟦_⟧ ⟫
