open import Framework.Definitions
module Framework.Variability.Soundness (V : 𝕍) where

open import Framework.Variant V
open import Framework.VariabilityLanguage
open import Data.Product using (_,_; _×_; ∃-syntax; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Function using (_∘_)

open import Framework.Function.Properties.Soundness VariantSetoid ℕ (Fin ∘ suc) public
open import Framework.Function.Proof.Soundness VariantSetoid ℕ (Fin ∘ suc) public

-- import Framework.Function.Properties.Soundness as FL

-- This encodes semantic domains that are finite (fin) and not empty (suc)
-- open import Framework.Function.Properties.Soundness V ℕ (Fin ∘ suc) public

-- Sound : VariabilityLanguage V → Set₁
-- Sound Lang-⟪ Expr , _ , ⟦_⟧ ⟫ =
--   ∀ {A} → let open IVSet A in
--   ∀ (e : Expr A)
--     --------------------------------
--   → ∃[ n ] Σ[ m ∈ VMap A n ] m ≅ ⟦ e ⟧

-- Unsound : VariabilityLanguage V → Set₁
-- Unsound L = ¬ (Sound L)
