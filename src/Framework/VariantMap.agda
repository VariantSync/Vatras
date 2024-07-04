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
As a representative set, we use Fin (suc n) to ensure that variant maps
are finite (Fin) and non-empty (suc n) indexed sets.
Using (suc n) here is a shortcut to ensure that the index set has at
least one element and hence is not empty.
-}
VMap : ℕ → Set₁
VMap n = IndexedSet (Fin (suc n))

{-|
This function removes the first variant from a variant map.
Given that we use natural numbers as an index set for variant maps,
variant maps have an implicit total order.
Hence, we can distinguish the first element.
-}
remove-first : ∀ {n} → VMap (suc n) → VMap n
remove-first set i = set (Data.Fin.suc i)

{-|
This function removes the last variant from a variant map.
Given that we use natural numbers as an index set for variant maps,
variant maps have an implicit total order.
Hence, we can distinguish the last element.
-}
remove-last : ∀ {n} → VMap (suc n) → VMap n
remove-last set i = set (Data.Fin.inject₁ i)

