{-# OPTIONS --sized-types --guardedness #-}

module Main where

open import Data.String
open import Data.List
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; _>>_; Main)
open import Level using (Level; 0ℓ)
open import Size using (∞)

open import Test.Example using (Example)
open import Test.Experiment using (Experiment; linebreak; runAll)

open import Lang.CCC using (CCC)
open import Lang.OC using (WFOC)

open import Test.Examples.CCC using (ccex-all)
open import Test.Examples.OC using (optex-all)

open import Test.Experiments.CCC-to-BCC
open import Test.Experiments.OC-yes-no
open import Test.Experiments.OC-to-BCC

experimentsToRun : List (∃[ A ] (Experiment A × List (Example A)))
experimentsToRun =
    (CCC  ∞ String , exp-to-binary-and-back , ccex-all) ∷
    (WFOC ∞ String , exp-run-allyes-and-allno , optex-all) ∷
    (WFOC ∞ String , exp-oc-to-bcc , optex-all) ∷
  []

main : Main
main = IO.run do
  IO.putStrLn "It's dangerous to go alone! Take this uncode to see if your terminal supports it:"
  IO.putStrLn "⟦ ₙ ● ∘ ⟨ ❲❳"
  IO.putStrLn "... but now on to the actual stuff."
  linebreak
  let runEntry = λ (A , exp , exa) → runAll exp exa
  linebreak
  IO.List.mapM′ runEntry experimentsToRun
  linebreak

