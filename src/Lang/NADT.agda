module Lang.NADT where

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Util.List using (find-or-last)

{-
A generalisation of algebraic decision trees
to choices with an arbitrary number of alternatives (at least one though) just
as in core choice calculus CCC.
This language is to ADT, what CCC is to 2CC.
-}
data NADT (V : 𝕍) (F : 𝔽) : Size → 𝔼 where
  leaf : ∀ {i A} → V A → NADT V F (↑ i) A
  _⟨_⟩ : ∀ {i A} → F → List⁺ (NADT V F i A) → NADT V F (↑ i) A

-- configurations pick an alternative to select
Configuration : (F : 𝔽) → ℂ
Configuration F = F → ℕ

{-|
The semantics of NADTs has the same semantics as
ADTs have for leaf,
CCC has for choices.
-}
⟦_⟧ : ∀ {i : Size} {V : 𝕍} {F : 𝔽} → 𝔼-Semantics V (Configuration F) (NADT V F i)
⟦ leaf v   ⟧ conf = v
⟦ f ⟨ cs ⟩ ⟧ conf = ⟦ find-or-last (conf f) cs ⟧ conf

NADTL : ∀ {i : Size} (V : 𝕍) (F : 𝔽) → VariabilityLanguage V
NADTL {i} V F = ⟪ NADT V F i , Configuration F , ⟦_⟧ ⟫
