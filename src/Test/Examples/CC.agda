{-# OPTIONS --sized-types #-}
module Test.Examples.CC where

open import Data.String using (String)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Product
  using (_,_; _×_)
open import Size
  using (Size; ∞; ↑_)

open import Lang.CCC
open import Test.Example

CCExample : Set
CCExample = Example (CCC ∞ String)

-- some smart constructors
chcA : ∀ {i : Size} {A : Set} → List⁺ (CCC i A) → CCC (↑ i) A
chcA es = "A" ⟨ es ⟩

chcA-leaves : ∀ {i : Size} {A : Set} → List⁺ A → CCC (↑ ↑ i) A
chcA-leaves es = chcA (leaves es)

-- examples

ccex-ekko : CCExample
ccex-ekko = "ekko" example: cc_example_walk

ccex-binary : CCExample
ccex-binary = "binary" example: "D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩

ccex-binary-nested : CCExample
ccex-binary-nested = "binary-nested" example:
  "A" ⟨ ("A" ⟨ leaf "1" ∷ leaf "2" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "3" ∷ leaf "4" ∷ [] ⟩) ∷ []
      ⟩

ccex-ternary-nested : CCExample
ccex-ternary-nested = "ternary-nested" example:
  chcA ( chcA-leaves ("1" ∷ "2" ∷ "3" ∷ []) ∷
         chcA-leaves ("4" ∷ "5" ∷ "6" ∷ []) ∷
         chcA-leaves ("7" ∷ "8" ∷ "9" ∷ []) ∷ [])

ccex-complex1 : CCExample
ccex-complex1 = "complex1" example:
  "A" ⟨ ("B" ⟨ leaf "1" ∷ leaf "2" ∷ leaf "3" ∷ [] ⟩) ∷
        ("C" ⟨ leaf "c" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "4" ∷
               ("D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩) ∷
               leaf "5" ∷ []
             ⟩) ∷ []
      ⟩

ccex-nametrick : CCExample
ccex-nametrick = "name-trick" example:
  "A" ⟨ ("A.0" ⟨ leaf "A.0-left" ∷ leaf "A.0-right" ∷ [] ⟩) ∷ leaf "x" ∷ [] ⟩

ccex-all : List CCExample
ccex-all =
  ccex-ekko ∷
  ccex-binary ∷
  ccex-binary-nested ∷
  ccex-ternary-nested ∷
  ccex-complex1 ∷
  ccex-nametrick ∷
  []
