{-# OPTIONS --sized-types --guardedness #-}

module Main where

open import Data.String
open import Data.List
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; _>>_; Main)
open import Level using (Level; 0ℓ)
open import Size using (∞)

open import Lang.CCC using (CCC)

open import Test.Example using (Example)
open import Test.Experiment using (Experiment; linebreak; runAll)
open import Test.Examples.CC using (ccex-all)

open import Test.Experiments.CCC-to-BCC

experimentsToRun : List (∃[ A ] (Experiment A × List (Example A)))
experimentsToRun =
    (CCC ∞ String , toBinaryAndBack , ccex-all) ∷
  []

main : Main
main = IO.run do
  let runEntry = λ (A , exp , exa) → runAll exp exa
  linebreak
  IO.List.mapM′ runEntry experimentsToRun
  linebreak

