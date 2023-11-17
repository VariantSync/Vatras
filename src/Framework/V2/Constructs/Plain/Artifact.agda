module Framework.V2.Constructs.Plain.Artifact where

open import Data.List using (List; map)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

record Artifact {ℓ₁ ℓ₂} (N : Set ℓ₁) (C : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _-<_>-
  field
    val : N
    children : List C

map-children :
  ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} {C₁ C₂ : Set ℓ₂}
  → (translation : C₁ → C₂)
  → Artifact N C₁
  → Artifact N C₂
map-children t (a -< es >-) = a -< map t es >-
