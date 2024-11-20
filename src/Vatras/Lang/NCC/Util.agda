open import Vatras.Framework.Definitions
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥)
module Vatras.Lang.NCC.Util {Dimension : 𝔽} {n : ℕ≥ 2} where

open import Size using (Size)
open import Data.List as List using (List; _∷_)
import Data.Vec as Vec

open import Vatras.Lang.NCC Dimension n using (NCC; _⟨_⟩; _-<_>-)

{-
Recursively, collect all dimensions used in an n-CC expression:
-}
dims : ∀ {i : Size} {A : 𝔸} → NCC i A → List Dimension
dims (_ -< es >-) = List.concatMap dims es
dims (D ⟨ cs ⟩) = D ∷ List.concatMap dims (Vec.toList cs)
