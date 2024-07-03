module Test.Examples.CCC where

open import Data.String as String using (String)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to map⁺)
open import Data.Product
  using (_,_; _×_)
open import Size
  using (Size; ∞; ↑_)

open import Framework.Definitions using (𝔸; atoms)

open import Lang.All
open CCC -- use strings as dimensions
open import Test.Example

CCCExample : Set₁
CCCExample = Example (CCC String ∞ (String , String._≟_))

-- some smart constructors
ccA : ∀ {i : Size} {A : 𝔸} → List⁺ (CCC String i A) → CCC String (↑ i) A
ccA es = "A" ⟨ es ⟩

cc-leaf : ∀ {i : Size} {A : 𝔸} → (atoms A) → CCC String (↑ i) A
cc-leaf a = a -< [] >-

cc-leaves : ∀ {i : Size} {A : 𝔸} → String → List⁺ (atoms A) → CCC String (↑ ↑ i) A
cc-leaves D es = D ⟨ map⁺ cc-leaf es ⟩

ccA-leaves : ∀ {i : Size} {A : 𝔸} → List⁺ (atoms A) → CCC String (↑ ↑ i) A
ccA-leaves = cc-leaves "A"

-- examples

cccex-binary : CCCExample
cccex-binary = "binary" ≔ "D" ⟨ cc-leaf "left" ∷ cc-leaf "right" ∷ [] ⟩

cccex-binary-nested : CCCExample
cccex-binary-nested = "binary-nested" ≔
  "A" ⟨ ("A" ⟨ cc-leaf "1" ∷ cc-leaf "2" ∷ [] ⟩) ∷
        ("A" ⟨ cc-leaf "3" ∷ cc-leaf "4" ∷ [] ⟩) ∷ []
      ⟩

cccex-ternary-nested : CCCExample
cccex-ternary-nested = "ternary-nested" ≔
  ccA ( ccA-leaves ("1" ∷ "2" ∷ "3" ∷ []) ∷
        ccA-leaves ("4" ∷ "5" ∷ "6" ∷ []) ∷
        ccA-leaves ("7" ∷ "8" ∷ "9" ∷ []) ∷ [])

cccex-complex1 : CCCExample
cccex-complex1 = "complex1" ≔
  "A" ⟨ (cc-leaves "B" ("1" ∷ "2" ∷ "3" ∷ [])) ∷
        (cc-leaves "C" ("c" ∷ [])) ∷
        ("A" ⟨ cc-leaf "4" ∷
               (cc-leaves "D" ("left" ∷ "right" ∷ [] )) ∷
               cc-leaf "5" ∷ []
             ⟩) ∷ []
      ⟩

cccex-all : List CCCExample
cccex-all =
  cccex-binary ∷
  cccex-binary-nested ∷
  cccex-ternary-nested ∷
  cccex-complex1 ∷
  []
