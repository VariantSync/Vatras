module Framework.VariabilityLanguage where

open import Data.Unit using (⊤)

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

VariabilityLanguage : (V : 𝕍) → Set₁
VariabilityLanguage = FunctionLanguage
pattern Lang-⟪_,_,_⟫ E C S = ⟪ E , C , S ⟫

Expression = FunctionLanguage.Expression
Config     = FunctionLanguage.Input
Semantics  = FunctionLanguage.Semantics
