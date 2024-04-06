{-# OPTIONS --large-indices --no-forced-argument-recursion #-}

open import Framework.Definitions
module Lang.ADT where

open import Data.Bool using (Bool; if_then_else_)
open import Framework.VariabilityLanguage

data ADT (V : 𝕍) (F : 𝔽) : 𝔼 where
  leaf   : ∀ {A} → V A → ADT V F A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : ADT V F A) → (r : ADT V F A) → ADT V F A

Configuration : (F : 𝔽) → Set
Configuration F = F → Bool

⟦_⟧ : {V : 𝕍} → {F : 𝔽} → 𝔼-Semantics V (Configuration F) (ADT V F)
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

ADTL : (V : 𝕍) → (F : 𝔽) → VariabilityLanguage V
ADTL V F = ⟪ ADT V F , Configuration F , ⟦_⟧ ⟫


open import Data.String as String using (String; _++_; intersperse)
open import Data.Product using (_,_)
open import Show.Lines

pretty : {A : 𝔸} → {V : 𝕍} → {F : 𝔽} → (V A → String) → (F → String) → ADT V F A → Lines
pretty pretty-variant show-F (leaf v) = > pretty-variant v
pretty pretty-variant show-F (D ⟨ l , r ⟩) = do
  > show-F D ++ "⟨"
  indent 2 do
    appendToLastLine "," (pretty pretty-variant show-F l)
    pretty pretty-variant show-F r
  > "⟩"
