open import Framework.Definitions
module Lang.2ADT (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (Bool; if_then_else_)
open import Framework.VariabilityLanguage

data 2ADT : 𝔼 where
  leaf   : ∀ {A} → V A → 2ADT A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : 2ADT A) → (r : 2ADT A) → 2ADT A

Configuration : Set
Configuration = F → Bool

⟦_⟧ : 𝔼-Semantics V Configuration 2ADT
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

2ADTL : VariabilityLanguage V
2ADTL = ⟪ 2ADT , Configuration , ⟦_⟧ ⟫
