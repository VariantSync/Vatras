open import Framework.Definitions
module Lang.ADT where

open import Data.Bool using (Bool; if_then_else_)
open import Framework.VariabilityLanguage

data ADT (F : 𝔽) : 𝔼 where
  leaf   : ∀ {A} → Variant A → ADT F A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : ADT F A) → (r : ADT F A) → ADT F A

Configuration : (F : 𝔽) → Set
Configuration F = F → Bool

⟦_⟧ : {F : 𝔽} → 𝔼-Semantics (Configuration F) (ADT F)
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

ADTL : (F : 𝔽) → VariabilityLanguage
ADTL F = ⟪ ADT F , Configuration F , ⟦_⟧ ⟫


open import Data.String as String using (String; _++_; intersperse)
open import Data.Product using (_,_)
open import Show.Lines

pretty : {A : 𝔸} → {F : 𝔽} → (Variant A → String) → (F → String) → ADT F A → Lines
pretty pretty-variant show-F (leaf v) = > pretty-variant v
pretty pretty-variant show-F (D ⟨ l , r ⟩) = do
  > show-F D ++ "⟨"
  indent 2 do
    appendToLastLine "," (pretty pretty-variant show-F l)
    pretty pretty-variant show-F r
  > "⟩"
