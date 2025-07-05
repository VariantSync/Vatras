open import Vatras.Framework.Definitions
module Vatras.Lang.ADT.Prop (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (if_then_else_)
open import Vatras.Data.Prop using (Prop; Assignment; eval)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Lang.ADT (Prop F) V

⟦_⟧ₚ : 𝔼-Semantics V (Assignment F) ADT
⟦ e ⟧ₚ c = ⟦ e ⟧ (λ D → eval D c)

PropADTL : VariabilityLanguage V
PropADTL = ⟪ ADT , Assignment F , ⟦_⟧ₚ ⟫
