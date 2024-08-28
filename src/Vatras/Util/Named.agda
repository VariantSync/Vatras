module Vatras.Util.Named where

open import Data.String using (String; _++_)

{-|
Record to hold a value with a name.
-}
record Named {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _called_
  field
    get : A
    getName : String
open Named public
infix 2 _called_

map-named : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → Named A → Named B
map-named f (get called name) = f get called name

show-named : ∀ {ℓ} {A : Set ℓ} → (A → String) → Named A → String
show-named show-A n = (getName n) ++ " = " ++ show-A (get n)
