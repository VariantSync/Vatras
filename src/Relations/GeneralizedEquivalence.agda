open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (
  IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous using (
  IRel;
  IsIndexedEquivalence)

module Relations.GeneralizedEquivalence where

{-|
Unwraps an indexed equivalence.
-}
iseq : ∀ {i a ℓ : Level} {I : Set i} {A : I → Set a} {_≈_ : IRel A ℓ}
  → IsIndexedEquivalence A _≈_
  → ∀ {x : I} → IsEquivalence (_≈_ {x})
iseq ieq = record
  { refl  = IsIndexedEquivalence.refl  ieq
  ; sym   = IsIndexedEquivalence.sym   ieq
  ; trans = IsIndexedEquivalence.trans ieq
  }


-- open import Level using (Level; suc; _⊔_)
-- open import Relation.Binary using (REL; Reflexive; Sym; Trans)

-- module Relations.GeneralizedEquivalence
--   {a ℓ : Level}
--   (_≈_ : ∀ {A B : Set a} → REL A B ℓ)
--   where

-- record IsEQUIVALENCE : Set (suc (a ⊔ ℓ)) where
--   field
--     refl  : ∀ {A} → Reflexive (_≈_ {A} {A})
--     sym   : ∀ {A B} → Sym (_≈_ {A} {B}) (_≈_ {B} {A})
--     trans : ∀ {A B C} → Trans (_≈_ {A} {B}) (_≈_ {B} {C}) (_≈_ {A} {C})

