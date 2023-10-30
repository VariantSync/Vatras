module Framework.V2.Variants where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Framework.V2.Definitions using (𝕍; 𝔸)

import Data.IndexedSet

data GrulerVariant {ℓ} : 𝕍 ℓ where
  asset : ∀ {A : 𝔸 ℓ} (a : A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸 ℓ} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

VariantSetoid : ∀ {ℓ} → 𝕍 ℓ → 𝔸 ℓ → Setoid ℓ ℓ
VariantSetoid V A = Eq.setoid (V A)

module IVSet {ℓ} (V : 𝕍 ℓ) (A : 𝔸 ℓ) = Data.IndexedSet (VariantSetoid V A)

IndexedVMap : ∀ {ℓ i} → 𝕍 ℓ → 𝔸 ℓ → Set i → Set (ℓ ⊔ i)
IndexedVMap V A I = IndexedSet I
  where open IVSet V A using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : ∀ {ℓ} → 𝕍 ℓ → 𝔸 ℓ → ℕ → Set ℓ
VMap V A n = IndexedVMap V A (Fin (suc n))
