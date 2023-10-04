module Framework.V2.Variants where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Framework.V2.Definitions using (𝕍; 𝔸)

import Data.IndexedSet

private
  variable
    A : 𝔸

data GrulerVariant : 𝕍 where
  asset : (a : A) → GrulerVariant A
  _∥_   : (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

VariantSetoid : 𝕍 → 𝔸 → Setoid 0ℓ 0ℓ
VariantSetoid V A = Eq.setoid (V A)

IndexedVMap : 𝕍 → 𝔸 → Set → Set
IndexedVMap V A I = IndexedSet I
  where open Data.IndexedSet (VariantSetoid V A) using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : 𝕍 → 𝔸 → ℕ → Set
VMap V A n = IndexedVMap V A (Fin (suc n))
