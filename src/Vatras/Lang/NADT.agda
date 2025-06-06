open import Vatras.Framework.Definitions

module Vatras.Lang.NADT (F : 𝔽) (V : 𝕍) where

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺)
open import Function using (id)
open import Size using (Size; ↑_)

open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Variants using (GrulerVariant)
open import Vatras.Util.List using (find-or-last)

{-|
A generalisation of algebraic decision trees
to choices with an arbitrary number of alternatives (at least one though) just
as in core choice calculus CCC.
This language is to ADT, what CCC is to 2CC.
-}
data NADT : Size → 𝔼 where
  leaf : ∀ {i A} → V A → NADT (↑ i) A
  _⟨_⟩ : ∀ {i A} → F → List⁺ (NADT i A) → NADT (↑ i) A

-- configurations pick an alternative to select
Configuration : ℂ
Configuration = F → ℕ

{-|
The semantics of NADTs has the same semantics as
ADTs have for leaf,
CCC has for choices.
-}
⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics V Configuration (NADT i)
⟦ leaf v   ⟧ conf = v
⟦ f ⟨ cs ⟩ ⟧ conf = ⟦ find-or-last (conf f) cs ⟧ conf

NADTL : ∀ {i : Size} → VariabilityLanguage V
NADTL {i} = ⟪ NADT i , Configuration , ⟦_⟧ ⟫
