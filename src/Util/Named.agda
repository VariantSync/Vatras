module Util.Named where

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

show-named : ∀ {ℓ} {A : Set ℓ} → (A → String) → Named A → String
show-named show-A n = (getName n) ++ " = " ++ show-A (get n)
