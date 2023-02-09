{-# OPTIONS --sized-types --guardedness #-}

module Main where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Size using (∞)

open import Show.Lines
open import Show.Print

open import Test.Example using (Example)
open import Test.Experiment using (Experiment; runAll)

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

main_lines : Lines
main_lines = do
  linebreak
  > "It's dangerous to go alone! Take this unicode to see whether your terminal supports it:"
  > "  ₙ ₁ ₂ 𝑎 𝑏 ⟦ ⟧ ⟨ ⟩ ❲❳"
  > "... but now on to the actual stuff."
  linebreak
  let runEntry = λ (A , exp , exa) → runAll exp exa
  linebreak
  overwrite-alignment-with
    Center
    (lines (map runEntry experimentsToRun))

open import IO using (IO; Main; putStrLn)

-- minor todo: use haskell to get width of current terminal
TERMINAL-WIDTH = 120

main : Main
main = IO.run (print TERMINAL-WIDTH main_lines)
