-- Defines equational reasoning for some of our semantic equivalences
module SemanticEquationalReasoning where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)

open import CC using (CC; _≈_)

module _≈_-Reasoning {A : Set} where
  infix  1 ≈-begin_
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_
  infix  3 _≈-∎

  ≈-begin_ : ∀ {a b : CC A}
    → a ≈ b
      -----
    → a ≈ b
  ≈-begin eq = eq

  _≈⟨⟩_ : ∀ (a : CC A) {b : CC A}
    → a ≈ b
      -----
    → a ≈ b
  a ≈⟨⟩ a≈b = a≈b

  _≈⟨_⟩_ : ∀ (a : CC A) {b c : CC A}
    → a ≈ b
    → b ≈ c
      -----
    → a ≈ c
  a ≈⟨ a≈b ⟩ b≈c = Eq.trans a≈b b≈c

  _≈-∎ : ∀ (a : CC A)
      -----
    → a ≈ a
  a ≈-∎ = refl

