open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
module Framework.Variability.Soundness (V : Setoid 0ℓ 0ℓ) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Function using (_∘_)

-- This encodes semantic domains that are finite (fin) and not empty (suc)
open import Framework.Function.Properties.Soundness V ℕ (Fin ∘ suc) public
