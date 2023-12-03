module Framework.VariabilityLanguage where

open import Framework.Definitions
open import Framework.Variant
open import Framework.FunctionLanguage as FL
open import Framework.ConfigurationLanguage as CL using (ConfigurationLanguage; Configuration)

{-
Semantics of variability languages.
The semantics of a set of expressions `E : 𝔼` is a function
that configures a term `e : E A` to a variant `v : V A`
-}
𝔼-Semantics : 𝕍 → 𝕂 → 𝔼 → Set₁
𝔼-Semantics V K E =
  ∀ {A : 𝔸}
  → E A
  → K
  → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage (V : 𝕍) : Set₁ where
  constructor Lang-⟪_,_,_⟫
  field
    Expression : 𝔼
    Config     : 𝕂
    Semantics  : 𝔼-Semantics V Config Expression

  isFunctionLanguage : ∀ (A : 𝔸) → FunctionLanguage (V A)
  isFunctionLanguage A = ⟪ Expression A , Config , Semantics ⟫
open VariabilityLanguage public

