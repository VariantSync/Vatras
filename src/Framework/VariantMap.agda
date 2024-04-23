open import Framework.Definitions using (𝕍; 𝔸)
module Framework.VariantMap (V : 𝕍) (A : 𝔸) where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc)

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Data.EqIndexedSet {A = V A}

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : ℕ → Set₁
VMap n = IndexedSet (Fin (suc n))

-- Utility functions for manipulating variant maps.
remove-first : ∀ {n} → VMap (suc n) → VMap n
remove-first set i = set (Data.Fin.suc i)

remove-last : ∀ {n} → VMap (suc n) → VMap n
remove-last set i = set (Data.Fin.inject₁ i)

