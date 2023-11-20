open import Framework.V2.Definitions using (𝕍; 𝔸)
module Framework.V2.Variant (V : 𝕍) (A : 𝔸) where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc)

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

VariantSetoid : Setoid 0ℓ 0ℓ
VariantSetoid = Eq.setoid (V A)

module IVSet = Data.IndexedSet VariantSetoid

IndexedVMap : Set → Set
IndexedVMap I = IndexedSet I
  where open IVSet using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : ℕ → Set
VMap n = IndexedVMap (Fin (suc n))

forget-first : ∀ {n} → VMap (suc n) → VMap n
forget-first set i = set (Data.Fin.suc i)
