open import Framework.Definitions

module Construct.NestedChoice (F : 𝔽) where

open import Level using (suc)
open import Data.String using (String)
open import Size using (Size; ↑_)

open import Construct.Choices

data NestedChoice {ℓ} : Size → Set ℓ → Set (suc ℓ) where
  value  : ∀ {i A} → A → NestedChoice i A
  choice : ∀ {i A} → 2Choice.Syntax F (NestedChoice i A) → NestedChoice (↑ i) A

⟦_⟧ : ∀ {ℓ i A} → NestedChoice {ℓ} i A → 2Choice.Config F → A
⟦ value  v   ⟧ c = v
⟦ choice chc ⟧ c = ⟦ 2Choice.⟦ chc ⟧ c ⟧ c

show-nested-choice : ∀ {ℓ i A} → (F → String) → (A → String) → NestedChoice {ℓ} i A → String
show-nested-choice show-q show-carrier ( value v) = show-carrier v
show-nested-choice show-q show-carrier (choice c) =
  2Choice.show
    show-q
    (show-nested-choice show-q show-carrier)
    c
