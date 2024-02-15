-- open import Level using (0ℓ)
-- open import Relation.Binary using (Setoid)
open import Framework.Definitions
module Framework.Variability.Completeness (V : 𝕍) where

open import Framework.Variant V
open import Framework.VariabilityLanguage
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Function using (_∘_)

open import Framework.Function.Properties.Completeness VariantSetoid ℕ (Fin ∘ suc) public
open import Framework.Function.Proof.Completeness VariantSetoid ℕ (Fin ∘ suc) public

-- Complete : VariabilityLanguage V → Set₁
-- Complete Lang-⟪ Expr , _ , ⟦_⟧ ⟫ =
--   ∀ {A} → let open IVSet A in
--   ∀ {n} (vs : VMap A n)
--     --------------------------
--   → Σ[ e ∈ Expr A ] vs ≅ ⟦ e ⟧

-- Incomplete : VariabilityLanguage V → Set₁
-- Incomplete L = ¬ (Complete L)

-- VLComplete→FLComplete : ∀ (Γ : VariabilityLanguage V)
--   → Complete Γ
--   → ∀ (n : ℕ) → FL.Complete (Fin (suc n)) VariantSetoid Γ
-- VLComplete→FLComplete Γ x n m = x m

-- FLComplete→VLComplete : ∀ (Γ : VariabilityLanguage V)
--   → (∀ (n : ℕ) → FL.Complete (Fin (suc n)) VariantSetoid Γ)
--   → Complete Γ
-- FLComplete→VLComplete Γ comp {_} {n} vs = comp n vs

-- VLIncomplete→FLIncomplete : ∀ (Γ : VariabilityLanguage V)
--   → Incomplete Γ
--   → ¬ (∀ (n : ℕ) → FL.Complete (Fin (suc n)) VariantSetoid Γ)
-- VLIncomplete→FLIncomplete Γ incomp comp = incomp (FLComplete→VLComplete Γ comp)
