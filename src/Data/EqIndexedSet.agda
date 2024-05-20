open import Level using (Level)

module Data.EqIndexedSet {ℓ : Level} {A : Set ℓ} where

import Relation.Binary.PropositionalEquality as Eq
open import Data.IndexedSet {ℓ} (Eq.setoid A) as ISet public
