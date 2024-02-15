module Framework.ConfigurationLanguage where

open import Framework.Definitions
open import Framework.FunctionLanguage

ConfigurationLanguage : (S : 𝕊) → Set₁
ConfigurationLanguage S = FunctionLanguage λ _ → S
pattern Conf-⟪_,_,_⟫ E F S = ⟪ E , F , S ⟫

-- aliases
Configuration     = FunctionLanguage.Expression
FeatureLanguage   = FunctionLanguage.Input
SelectionLanguage : ∀ {S : 𝕊} → ConfigurationLanguage S → 𝕊
SelectionLanguage {S} _ = S
