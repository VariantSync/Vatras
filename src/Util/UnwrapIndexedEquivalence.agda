open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (
  IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous using (
  IRel;
  IsIndexedEquivalence)

module Util.UnwrapIndexedEquivalence where

{-|
Unwraps an indexed equivalence.
-}
unwrap-IndexedEquivalence : ∀ {i a ℓ : Level} {I : Set i} {A : I → Set a} {_≈_ : IRel A ℓ}
  → IsIndexedEquivalence A _≈_
  → ∀ {x : I} → IsEquivalence (_≈_ {x})
unwrap-IndexedEquivalence ieq = record
  { refl  = IsIndexedEquivalence.refl  ieq
  ; sym   = IsIndexedEquivalence.sym   ieq
  ; trans = IsIndexedEquivalence.trans ieq
  }

