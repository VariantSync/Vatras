module Test.Example where

open import Data.String using (String)

record Example (A : Set) : Set where
  constructor _example:_
  field
    name  : String
    value : A
infix 2 _example:_
open Example public

-- data Show (A : Set) : Set where
--   printer : (A → String) → Show A
