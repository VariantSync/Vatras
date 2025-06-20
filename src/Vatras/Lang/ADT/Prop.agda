open import Vatras.Framework.Definitions
module Vatras.Lang.ADT.Prop (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (if_then_else_)
open import Vatras.Data.Prop using (Prop; Assignment; eval)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Lang.ADT (Prop F) V

⟦_⟧ₚ : 𝔼-Semantics V (Assignment F) ADT
⟦ leaf v      ⟧ₚ c = v
⟦ D ⟨ l , r ⟩ ⟧ₚ c =
  if eval D c
  then ⟦ l ⟧ₚ c
  else ⟦ r ⟧ₚ c

PropADTL : VariabilityLanguage V
PropADTL = ⟪ ADT , Assignment F , ⟦_⟧ₚ ⟫
