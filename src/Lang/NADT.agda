open import Framework.Definitions
module Lang.NADT where

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.Construct
open import Framework.VariabilityLanguage
open import Framework.Variants using (GrulerVariant)
open import Util.List using (find-or-last)

data NADT (V : 𝕍) (F : 𝔽) : Size → 𝔼 where
  NADTAsset  : ∀ {i A} → V A → NADT V F (↑ i) A
  NADTChoice : ∀ {i A} → F → List⁺ (NADT V F i A) → NADT V F (↑ i) A

Configuration : (F : 𝔽) → Set
Configuration F = F → ℕ

mutual
  NADTL : ∀ {i : Size} (V : 𝕍) (F : 𝔽) → VariabilityLanguage V
  NADTL {i} V F = ⟪ NADT V F i , Configuration F , ⟦_⟧ ⟫

  ⟦_⟧ : ∀ {i : Size} {V : 𝕍} {F : 𝔽} → 𝔼-Semantics V (Configuration F) (NADT V F i)

  ⟦_⟧ (NADTAsset v) conf = v
  ⟦_⟧ (NADTChoice f cs) conf = ⟦ find-or-last (conf f) cs ⟧ conf
