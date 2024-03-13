open import Framework.Definitions
module Lang.2ADT (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (Bool; if_then_else_)
open import Framework.VariabilityLanguage

data 2ADT : 𝔼 where
  leaf   : ∀ {A} → V A → 2ADT A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : 2ADT A) → (r : 2ADT A) → 2ADT A

Configuration : Set
Configuration = F → Bool

⟦_⟧ : ∀ {A} → 2ADT A → Configuration → V A
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

2ADTVL : VariabilityLanguage V
2ADTVL = ⟪ 2ADT , Configuration , ⟦_⟧ ⟫
