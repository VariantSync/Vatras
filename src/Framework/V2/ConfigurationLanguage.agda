module Framework.V2.ConfigurationLanguage where

open import Framework.V2.Definitions
open import Framework.V2.FunctionLanguage

ConfigurationLanguage : (S : 𝕊) → Set₁
ConfigurationLanguage S = FunctionLanguage S
pattern Conf-⟪_,_,_⟫ E F S = ⟪ E , F , S ⟫

-- aliases
Configuration     = FunctionLanguage.Expression
FeatureLanguage   = FunctionLanguage.Input
SelectionLanguage : ∀ {S : 𝕊} → ConfigurationLanguage S → 𝕊
SelectionLanguage {S} _ = S
