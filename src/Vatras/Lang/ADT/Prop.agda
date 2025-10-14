open import Vatras.Framework.Definitions
module Vatras.Lang.ADT.Prop (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (if_then_else_)
open import Vatras.Data.Prop using (Prop; Assignment; eval)
open import Vatras.Framework.VariabilityLanguage

import Vatras.Lang.ADT
open Vatras.Lang.ADT using (ADT)
open Vatras.Lang.ADT (Prop F) V using (⟦_⟧)
open Vatras.Lang.ADT (Prop F) V using (leaf; _⟨_,_⟩) public

PropADT : 𝔼
PropADT = ADT (Prop F) V

⟦_⟧ₚ : 𝔼-Semantics V (Assignment F) PropADT
⟦ e ⟧ₚ c = ⟦ e ⟧ (λ D → eval D c)

PropADTL : VariabilityLanguage V
PropADTL = ⟪ PropADT , Assignment F , ⟦_⟧ₚ ⟫
