open import Level using (Level)

{-|
This module re-exports indexed sets but where the underlying
equivalence for the target set is fixed to propositional equality _≡_.
Importing this module should be your usual way of importing indexed sets.
-}
module Data.EqIndexedSet {ℓ : Level} {A : Set ℓ} where

import Relation.Binary.PropositionalEquality as Eq
open import Data.IndexedSet {ℓ} (Eq.setoid A) as ISet public

