open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
module Framework.Variability.Completeness (V : Setoid 0ℓ 0ℓ) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Function using (_∘_)

open import Framework.Function.Properties.Completeness V ℕ (Fin ∘ suc) public
open import Framework.Function.Proof.Completeness V ℕ (Fin ∘ suc) public
