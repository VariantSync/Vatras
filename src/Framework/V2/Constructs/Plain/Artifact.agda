module Framework.V2.Constructs.Plain.Artifact where

open import Data.List using (List; []; map)
open import Data.List.Properties using () renaming (≡-dec to ≡-dec-l)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Level using (_⊔_)
open import Function using (_∘_)

open import Relation.Nullary.Decidable using (Dec; yes; no; isYes; False; toWitnessFalse)
open import Relation.Binary using (Setoid; DecidableEquality)

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

root-equality : ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} {C : Set ℓ₂} {a b : N} {as bs : List C}
   → a -< as >- ≡ b -< bs >-
     -----------------------
   → a ≡ b
root-equality refl = refl

children-equality : ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} {C : Set ℓ₂} {a b : N} {as bs : List C}
   → a -< as >- ≡ b -< bs >-
     ------------------------
   → as ≡ bs
children-equality refl = refl

≡-dec : ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} {C : Set ℓ₂}
  → DecidableEquality N
  → DecidableEquality C
  → DecidableEquality (Artifact N C)
≡-dec ≡-dec-A ≡-dec-C (a -< as >-) (b -< bs >-) with ≡-dec-A a b | ≡-dec-l ≡-dec-C as bs
... | yes a≡b | yes as≡bs = yes (Eq.cong₂ _-<_>- a≡b as≡bs)
... | yes a≡b | no ¬as≡bs = no (¬as≡bs ∘ children-equality)
... | no ¬a≡b | _         = no (¬a≡b   ∘ root-equality)

{-|
Smart constructor for artifact without children.
-}
leaf : ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} (C : Set ℓ₂) → N → Artifact N C
leaf _ a = a -< [] >-

leaves : ∀ {ℓ₁ ℓ₂} {N : Set ℓ₁} (C : Set ℓ₂) → List N → List (Artifact N C)
leaves C = map (leaf C)
