-- This file exists just for temporary compatibility clone-and-own with the old framework.
-- This file should be removed once all changes are reintegrated back to the original framework.
module Framework.V1Compat where

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
import Data.IndexedSet

open import Framework.Definitions
open import Framework.Variant
open import Framework.VariabilityLanguage

private
  variable
    A : 𝔸

Complete : ∀ {V} → VariabilityLanguage V → Set₁
Complete {V} (Lang-⟪ L , _ , ⟦_⟧ ⟫) = ∀ {A n}
  → (vs : VMap V A n)
    ----------------------------------
  → Σ[ e ∈ L A ]
      let open IVSet V A renaming (_≅_ to _≋_)
        in vs ≋ ⟦ e ⟧
