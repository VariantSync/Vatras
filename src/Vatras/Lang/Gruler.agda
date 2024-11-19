{-|
This module defines Gruler's language as defined in our paper.
While the original formalization uses natural numbers to name choices, we allow any
kind of annotation language F here without any loss of generality.
-}
open import Vatras.Framework.Definitions
module Vatras.Lang.Gruler (F : 𝔽) where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Size using (Size; ↑_; ∞)
import Level

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Variants using (GrulerVariant; ε; asset; _∥_)

{-|
A simplified syntax of Gruler's language from:
Alexander Gruler. 2010. A Formal Approach to Software Product Families. Ph. D. Dissertation. TU München

-}
data Gruler : Size → 𝔼 where
  -- explicit syntax for an empty variant
  ntrl   : ∀ {i A} → Gruler i A
  -- an asset stores some atomic data in a leaf node
  asset  : ∀ {i A} → atoms A → Gruler i A
  -- parallel composition: This is a binary node in the abstract syntax tree without further information.
  _∥_    : ∀ {i A} → Gruler i A → Gruler i A → Gruler (↑ i) A
  -- a choice where the dimension / annotation is written right behind the choice operator ⊕
  _⊕[_]_ : ∀ {i A} → Gruler i A → F → Gruler i A → Gruler (↑ i) A

Configuration : ℂ
Configuration = F → Bool

⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics GrulerVariant Configuration (Gruler i)
⟦ ntrl       ⟧ _ = ε
⟦ asset a    ⟧ _ = asset a
⟦ l ∥ r      ⟧ c = ⟦ l ⟧ c ∥ ⟦ r ⟧ c
⟦ l ⊕[ f ] r ⟧ c = if c f
                   then ⟦ l ⟧ c
                   else ⟦ r ⟧ c

GrulerL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
GrulerL {i} = ⟪ Gruler i , Configuration , ⟦_⟧ ⟫
