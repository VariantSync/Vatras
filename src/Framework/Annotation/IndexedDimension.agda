{-
This module defines an annotation with equips another annotation with an index.
The index is bounded (i.e., it is a Fin).
IndexedDimension is used for conversions from NCC to NCC with lower arity (in particular 2).
TODO: Abstract this to not have pred? How does it relate to IndexedName?
-}
module Framework.Annotation.IndexedDimension where

open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Util.Nat.AtLeast using (ℕ≥; toℕ; pred)
open import Framework.Definitions using (𝔽)

IndexedDimension : 𝔽 → ℕ≥ 2 → 𝔽
IndexedDimension D n = D × Fin (toℕ (pred n))
