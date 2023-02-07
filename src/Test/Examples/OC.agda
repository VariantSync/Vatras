{-# OPTIONS --sized-types #-}

module Test.Examples.OC where

open import Data.List using (List; []; _∷_; [_])
open import Data.String using (String)
open import Size using (∞)

open import Lang.Annotation.Name using (Option)
open import Lang.OC

open import Test.Example

OCExample : Set
OCExample = Example (WFOC ∞ String)

optex-unary : OCExample
optex-unary = "unary" example: (Root "r" [ opt "O" (leaf "lol") ])

optex-lock : OCExample
optex-lock = "lock" example: (Root "void f() {" (
    leaf          "int bobedi = 3;"
  ∷ "Lock" ❲ leaf "lock();" ❳
  ∷ leaf          "magic(bobedi);"
  ∷ "Lock" ❲ leaf "unlock();" ❳
  ∷ []))

optex-sandwich : OCExample
optex-sandwich = "sandwich" example: (Root "Buns" (
    "Tomato?" ❲ leaf "Tomato" ❳
  ∷ "Salad?"  ❲ leaf "Salad"  ❳
  ∷ "Cheese?" ❲ leaf "Cheese" ❳
  ∷ leaf "Mayonnaise" -- we always put mayo on the sandwich
  ∷ []))

optex-all : List OCExample
optex-all = optex-unary ∷ optex-lock ∷ optex-sandwich ∷ []

