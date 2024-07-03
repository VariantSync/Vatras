open import Framework.Definitions
module Lang.Gruler (F : 𝔽) where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Size using (Size; ↑_; ∞)
import Level

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant; ε; asset; _∥_)

data Gruler : Size → 𝔼 where
  ntrl   : ∀ {i A} → Gruler i A
  asset  : ∀ {i A} → atoms A → Gruler i A
  _∥_    : ∀ {i A} → Gruler i A → Gruler i A → Gruler (↑ i) A
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

GrulerVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
GrulerVL {i} = ⟪ Gruler i , Configuration , ⟦_⟧ ⟫
