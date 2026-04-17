module Vatras.Test.Examples.OC where

open import Data.List using (List; []; _∷_; [_])
open import Data.String as String using (String)
open import Data.Product using (_,_)
open import Size using (Size; ↑_; ∞)

-- open import Framework.Annotation.Name using (Option)
open import Vatras.Framework.Definitions using (STRING)
open import Vatras.Lang.All
open OC using (WFOC; Root; _❲_❳; opt; oc-leaf)
open import Vatras.Lang.OC.Util using (singleton)

open import Vatras.Test.Example

OCExample : Set₁
OCExample = Example (WFOC String ∞ STRING)

optex-unary : OCExample
optex-unary = "unary" ≔ (Root "r" [ opt "O" (oc-leaf "a") ])

optex-lock : OCExample
optex-lock = "lock" ≔ (Root "void f() {" (
    oc-leaf          "int bobedi = 3;"
  ∷ "Lock" ❲ oc-leaf "lock();" ❳
  ∷ oc-leaf          "magic(bobedi);"
  ∷ "Lock" ❲ oc-leaf "unlock();" ❳
  ∷ []))

optex-sandwich : OCExample
optex-sandwich = "sandwich" ≔ (Root "Buns" (
    "Tomato?" ❲ oc-leaf "tomato" ❳
  ∷ "Salad?"  ❲ oc-leaf "salad"  ❳
  ∷ "Cheese?" ❲ oc-leaf "cheese" ❳
  ∷ oc-leaf "Mayo" -- we always put mayo on these sandwiches
  ∷ []))

optex-deep : OCExample
optex-deep = "deep" ≔
  (Root "A"
    (singleton "B"
      (singleton "C"
        ("O" ❲ oc-leaf "hi" ❳)) ∷ []))

optex-all : List OCExample
optex-all = optex-unary ∷ optex-lock ∷ optex-sandwich ∷ optex-deep ∷ []

