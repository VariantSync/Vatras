{-|
This module defines algebraic decision trees as defined in our paper.
-}
open import Vatras.Framework.Definitions
module Vatras.Lang.ADT (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (Bool; if_then_else_)
open import Vatras.Framework.VariabilityLanguage

{-|
An algebraic decision tree stores variants in leaf nodes
and decorates them with binary choices.
-}
data ADT : 𝔼 where
  leaf   : ∀ {A} → V A → ADT A
  _⟨_,_⟩ : ∀ {A} → (D : F) → (l : ADT A) → (r : ADT A) → ADT A

Configuration : ℂ
Configuration = F → Bool

{-|
To configure an ADT, we basically walk down from the root to the
leaf node holding the desired variant.
We do this by evaluating each choice until we hit a leaf.
-}
⟦_⟧ : 𝔼-Semantics V Configuration ADT
⟦ leaf v      ⟧ _ = v
⟦ D ⟨ l , r ⟩ ⟧ c = if c D
                    then ⟦ l ⟧ c
                    else ⟦ r ⟧ c

ADTL : VariabilityLanguage V
ADTL = ⟪ ADT , Configuration , ⟦_⟧ ⟫

open import Data.String as String using (String; _++_; intersperse)
open import Data.Product using (_,_)
open import Vatras.Show.Lines

{-|
Pretty printer for ADTs.
-}
pretty : {A : 𝔸} → (V A → String) → (F → String) → ADT A → Lines
pretty pretty-variant show-F (leaf v) = > pretty-variant v
pretty pretty-variant show-F (D ⟨ l , r ⟩) = do
  > show-F D ++ "⟨"
  indent 2 do
    appendToLastLine "," (pretty pretty-variant show-F l)
    pretty pretty-variant show-F r
  > "⟩"
