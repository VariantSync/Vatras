open import Vatras.Framework.Definitions using (𝔸)
module Vatras.SyntacticExpressiveness (A : 𝔸) where

open import Data.Nat as ℕ using (ℕ; _≤_; _>_; _*_)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Nullary.Negation using (¬_)
open import Size using (∞)

open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; Expression)

record SizedLang : Set₂ where
  field
    Lang : VariabilityLanguage (Rose ∞)
    size : Expression Lang A → ℕ
open SizedLang

_≤Size_ : SizedLang → SizedLang → Set₁
L₁ ≤Size L₂ =
  Σ[ n ∈ ℕ ]
  ∀ (e₂ : Expression (Lang L₂) A) →
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
      Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
    × size L₁ e₁ ≤ n * size L₂ e₂

_=Size_ : SizedLang → SizedLang → Set₁
L₁ =Size L₂ = L₁ ≤Size L₂ × L₂ ≤Size L₁

_≱Size_ : SizedLang → SizedLang → Set₁
L₁ ≱Size L₂ =
  ∀ (n : ℕ) →
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
  ∀ (e₂ : Expression (Lang L₂) A )
  → Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
  → size L₂ e₂ > n * size L₁ e₁

_<Size_ : SizedLang → SizedLang → Set₁
L₁ <Size L₂ = L₁ ≤Size L₂ × L₁ ≱Size L₂

-- TODO reflexivity
-- TODO transitivity
-- TODO antisymmetrie
