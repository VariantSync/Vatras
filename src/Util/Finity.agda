module Util.Finity where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality as Peq using (_≡_)

open import Relation.Binary using (Setoid)
open import Function using (id; Surjective)

open import Level using (_⊔_)

{-|
A set (i.e., a type) is finite if all of its instances can be enumerated.
params:
mod - A modification function on the size of the index that can be used to simultaneously encode that the set must be non-empty
IndexSet - A set of indices that should be proven finite. Given as a setoid because we need an equivalence relation to ensure that every index is enumerated.
-}
record FiniteAnd (mod : ℕ → ℕ) {ℓ} {c} (IndexSet : Setoid c ℓ) : Set (c ⊔ ℓ) where
  open Setoid IndexSet using (_≈_) renaming (Carrier to I)
  field
    {-| A lower bound of the number of indices in I. -}
    size : ℕ
    {-|
    Associates each index by a natural number < mod size.
    This is essentially the proof that I is finite.
    -}
    enumerate : Fin (mod size) → I
    {-|
    The enumeration has to be surjective to guarantee that we enumerated _every_ index
    and not just some of them.
    -}
    enumerate-is-surjective : Surjective _≡_ _≈_ enumerate
open FiniteAnd public

private
  Nothing  = id
  NonEmpty = suc

Finite : ∀ {ℓ} {c} (IndexSet : Setoid c ℓ) → Set (c ⊔ ℓ)
Finite = FiniteAnd Nothing

FiniteAndNonEmpty : ∀ {ℓ} {c} (IndexSet : Setoid c ℓ) → Set (c ⊔ ℓ)
FiniteAndNonEmpty = FiniteAnd NonEmpty
