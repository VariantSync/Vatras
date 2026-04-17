open import Vatras.Framework.Definitions using (𝔸; 𝕍)
module Vatras.Succinctness.DesignedDefinition (V : 𝕍) where

open import Data.Product using (Σ-syntax)
open import Data.Nat using (ℕ; _≤_; _*_)
open import Function using (id)

open import Vatras.Framework.VariabilityLanguage using (Expression)
open import Vatras.Framework.Relation.Expression V using (_,_⊢_≣_)
open import Vatras.Succinctness.Sizes using (SizedLang; Lang; size)

minimalExpression
  : {A : 𝔸} (VL : SizedLang V)
  → Expression (Lang VL) A
  → Set _
minimalExpression {A} VL e =
  ∀ (e' : Expression (Lang VL) A) (e≅e' : Lang VL , Lang VL ⊢ e ≣ e')
  → size VL e ≤ size VL e'

design
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : SizedLang V)
  → Set _
design f VL₁ VL₂ =
    Σ[ m ∈ ℕ ]
  ∀ (A : 𝔸)
    (e₁ : Expression (Lang VL₁) A)
    (e₂ : Expression (Lang VL₂) A)
  → Lang VL₁ , Lang VL₂ ⊢ e₁ ≣ e₂
  → minimalExpression VL₁ e₁
  → minimalExpression VL₂ e₂
  → size VL₁ e₁ ≤ m * f (size VL₂ e₂)

relation
  : (VL₁ VL₂ : SizedLang V)
  → Set _
relation = design id
