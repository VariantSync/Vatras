{-# OPTIONS --sized-types #-}

module Test.Examples.Variants where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Definitions using (VSet; leaf)

open import Test.Example

𝕍-123 : Example (VSet ℕ 2)
𝕍-123 = "123" example: set
  where set : VSet ℕ 2
        set zero = leaf 1
        set (suc zero) = leaf 2
        set (suc (suc zero)) = leaf 3

𝕍-lr : Example (VSet String 1)
getName 𝕍-lr = "lr"
get 𝕍-lr zero = leaf "left"
get 𝕍-lr (suc zero) = leaf "right"
