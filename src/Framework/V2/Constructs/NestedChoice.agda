{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions

module Framework.V2.Constructs.NestedChoice (F : 𝔽) where

open import Data.String using (String)
open import Size using (Size; ↑_)

import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂; show to show-2choice)

data NestedChoice : Size → 𝔼 where
  value  : ∀ {i A} → A → NestedChoice i A
  choice : ∀ {i A} → 2Choice F (NestedChoice i A) → NestedChoice (↑ i) A

⟦_⟧ : ∀ {i A} → NestedChoice i A → Config₂ F → A
⟦ value  v   ⟧ c = v
⟦ choice chc ⟧ c = ⟦ ⟦ chc ⟧₂ c ⟧ c

show-nested-choice : ∀ {i A} → (F → String) → (A → String) → NestedChoice i A → String
show-nested-choice show-q show-carrier ( value v) = show-carrier v
show-nested-choice show-q show-carrier (choice c) =
  show-2choice
    show-q
    (show-nested-choice show-q show-carrier)
    c
