module Util.Util where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; [])

-- true iff the given list is empty
empty? : ∀ {A : Set} → List A → Bool
empty? [] = true
empty? (x ∷ xs) = false
