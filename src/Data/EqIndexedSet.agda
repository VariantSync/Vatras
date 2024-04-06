module Data.EqIndexedSet {A : Set} where

import Relation.Binary.PropositionalEquality as Eq
open import Data.IndexedSet (Eq.setoid A) as ISet public
