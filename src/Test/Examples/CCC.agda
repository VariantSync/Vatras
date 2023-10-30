{-# OPTIONS --sized-types #-}
module Test.Examples.CCC where

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

CCCExample : Set
CCCExample = Example (CCC ∞ String)

-- some smart constructors
chcA : ∀ {i : Size} {A : Set} → List⁺ (CCC i A) → CCC (↑ i) A
chcA es = "A" ⟨ es ⟩

chcA-leaves : ∀ {i : Size} {A : Set} → List⁺ A → CCC (↑ ↑ i) A
chcA-leaves es = chcA (leaves es)

-- examples

cccex-ekko : CCCExample
cccex-ekko = "ekko" ≔ cc_example_walk

cccex-binary : CCCExample
cccex-binary = "binary" ≔ "D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩

cccex-binary-nested : CCCExample
cccex-binary-nested = "binary-nested" ≔
  "A" ⟨ ("A" ⟨ leaf "1" ∷ leaf "2" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "3" ∷ leaf "4" ∷ [] ⟩) ∷ []
      ⟩

cccex-ternary-nested : CCCExample
cccex-ternary-nested = "ternary-nested" ≔
  chcA ( chcA-leaves ("1" ∷ "2" ∷ "3" ∷ []) ∷
         chcA-leaves ("4" ∷ "5" ∷ "6" ∷ []) ∷
         chcA-leaves ("7" ∷ "8" ∷ "9" ∷ []) ∷ [])

cccex-complex1 : CCCExample
cccex-complex1 = "complex1" ≔
  "A" ⟨ ("B" ⟨ leaf "1" ∷ leaf "2" ∷ leaf "3" ∷ [] ⟩) ∷
        ("C" ⟨ leaf "c" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "4" ∷
               ("D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩) ∷
               leaf "5" ∷ []
             ⟩) ∷ []
      ⟩

cccex-nametrick : CCCExample
cccex-nametrick = "name-trick" ≔
  "A" ⟨ ("A.0" ⟨ leaf "A.0-left" ∷ leaf "A.0-right" ∷ [] ⟩) ∷ leaf "x" ∷ [] ⟩

cccex-all : List CCCExample
cccex-all =
  cccex-ekko ∷
  cccex-binary ∷
  cccex-binary-nested ∷
  cccex-ternary-nested ∷
  cccex-complex1 ∷
  cccex-nametrick ∷
  []
