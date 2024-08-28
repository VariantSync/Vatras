{-|
Utility functions for pretty printing.
-}
module Vatras.Util.ShowHelpers where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; map)
open import Data.String using (String; _++_; intersperse)

show-bool : Bool → String
show-bool true  = "true"
show-bool false = "false"

{-|
Creates a string that shows the value of a function at a given point.
-}
show-fun-at : ∀ {A B : Set}
  → (A → String) -- print input values
  → (B → String) -- print output values
  → (A → B)
  → A
  → String
show-fun-at show-a show-b f a = show-a a ++ " ↦ " ++ show-b (f a)

{-|
Creates a string that shows the values of a function at all given points.
-}
show-fun : {A B : Set}
  → (A → String)
  → (B → String)
  → (A → B)
  → List A
  → String
show-fun show-a show-b f as = "{ " ++ intersperse ", " (map (show-fun-at show-a show-b f) as) ++ " }"
