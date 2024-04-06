open import Framework.Definitions
module Lang.2ADT where

open import Data.Bool using (Bool; if_then_else_)
open import Framework.VariabilityLanguage

data 2ADT (V : 𝕍) (F : 𝔽) : 𝔼 where
  leaf   : ∀ {A} → V A → 2ADT V F A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : 2ADT V F A) → (r : 2ADT V F A) → 2ADT V F A

Configuration : (F : 𝔽) → Set
Configuration F = F → Bool

⟦_⟧ : {V : 𝕍} → {F : 𝔽} → 𝔼-Semantics V (Configuration F) (2ADT V F)
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

2ADTL : (V : 𝕍) → (F : 𝔽) → VariabilityLanguage V
2ADTL V F = ⟪ 2ADT V F , Configuration F , ⟦_⟧ ⟫


open import Data.String as String using (String; _++_; intersperse)
open import Data.Product using (_,_)
open import Show.Lines

pretty : {A : 𝔸} → {V : 𝕍} → {F : 𝔽} → (V A → String) → (F → String) → 2ADT V F A → Lines
pretty pretty-variant show-F (leaf v) = > pretty-variant v
pretty pretty-variant show-F (D ⟨ l , r ⟩) = do
  > show-F D ++ "⟨"
  indent 2 do
    pretty pretty-variant show-F l
    > ","
    pretty pretty-variant show-F r
  > "⟩"
