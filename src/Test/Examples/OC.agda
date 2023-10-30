{-# OPTIONS --sized-types #-}

module Test.Examples.OC where

open import Data.List using (List; []; _∷_; [_])
open import Data.String using (String)
open import Size using (Size; ↑_; ∞)

open import Framework.Annotation.Name using (Option)
open import Framework.Definitions using (𝔸)
open import Lang.OC

open import Test.Example

OCExample : Set
OCExample = Example (WFOC ∞ String)

singleton : ∀ {i : Size} {A : 𝔸} → A → OC i A → OC (↑ i) A
singleton a e = Artifact a [ e ]

optex-unary : OCExample
optex-unary = "unary" ≔ (Root "r" [ opt "O" (oc-leaf "lol") ])

optex-lock : OCExample
optex-lock = "lock" ≔ (Root "void f() {" (
    oc-leaf          "int bobedi = 3;"
  ∷ "Lock" ❲ oc-leaf "lock();" ❳
  ∷ oc-leaf          "magic(bobedi);"
  ∷ "Lock" ❲ oc-leaf "unlock();" ❳
  ∷ []))

optex-sandwich : OCExample
optex-sandwich = "sandwich" ≔ (Root "Buns" (
    "Tomato?" ❲ oc-leaf "Tomato" ❳
  ∷ "Salad?"  ❲ oc-leaf "Salad"  ❳
  ∷ "Cheese?" ❲ oc-leaf "Cheese" ❳
  ∷ oc-leaf "Mayonnaise" -- we always put mayo on the sandwich
  ∷ []))

optex-deep : OCExample
optex-deep = "deep" ≔
  (Root "A"
    (singleton "B"
      (singleton "C"
        ("O" ❲ oc-leaf "hi" ❳)) ∷ []))

optex-all : List OCExample
optex-all = optex-unary ∷ optex-lock ∷ optex-sandwich ∷ optex-deep ∷ []

