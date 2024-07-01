open import Framework.Definitions
module Lang.Gruler (F : 𝔽) where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Size using (Size; ↑_; ∞)
import Level

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant; asset; _∥_)
open import Framework.Construct

data Gruler : Size → 𝔼 where
  GAsset  : ∀ {i A} → atoms A → Gruler i A
  GPComp  : ∀ {i A} → Gruler i A → Gruler i A → Gruler (↑ i) A
  GChoice : ∀ {i A} → F → Gruler i A → Gruler i A → Gruler (↑ i) A

Configuration : 𝕂
Configuration = F → Bool

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant Configuration (Gruler i)

GrulerVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant
GrulerVL {i} = ⟪ Gruler i , Configuration , semantics ⟫

semantics (GAsset a) _ = asset a
semantics (GPComp l r) conf = semantics l conf ∥ semantics r conf
semantics (GChoice d l r) conf = semantics (if conf d then l else r) conf
