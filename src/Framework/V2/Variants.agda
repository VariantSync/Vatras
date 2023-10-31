module Framework.V2.Variants where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc)

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Framework.V2.Definitions using (𝕍; 𝔸)

import Data.IndexedSet

data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} (a : A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

data WalkingshawVariant : 𝕍 where
  -- TODO: Use Artifact Construct here.
  _-<_>- : ∀ {A : 𝔸} (a : A) → List (WalkingshawVariant A) → WalkingshawVariant A

VariantSetoid : 𝕍 → 𝔸 → Setoid 0ℓ 0ℓ
VariantSetoid V A = Eq.setoid (V A)

module IVSet (V : 𝕍) (A : 𝔸) = Data.IndexedSet (VariantSetoid V A)

IndexedVMap : 𝕍 → 𝔸 → Set → Set
IndexedVMap V A I = IndexedSet I
  where open IVSet V A using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : 𝕍 → 𝔸 → ℕ → Set
VMap V A n = IndexedVMap V A (Fin (suc n))
