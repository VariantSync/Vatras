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

open import Test.Examples.CCC using (cccex-all)
open import Test.Examples.OC using (optex-all)

open import Test.Experiments.CCC-to-BCC
open import Test.Experiments.OC-to-BCC

{-|
A list of programs that we want to run.
Each program is implemented in terms of an Experiment.
Each experiment is run on each example from a list of examples (i.e., experiment inputs).
-}
experimentsToRun : List (∃[ A ] (Experiment A × List (Example A)))
experimentsToRun =
    -- Run some example translations from n-ary to binary choice calculus
    (CCC  ∞ String , exp-to-binary-and-back , cccex-all) ∷
    -- Run some example translations of option calculus to binary choice calculus
    (WFOC ∞ String ,          exp-oc-to-bcc , optex-all) ∷
  []

{-|
Implementation of what the main method should print.
-}
main_lines : Lines
main_lines = do
  linebreak
  > "It's dangerous to go alone! Take this unicode to see whether your terminal supports it:"
  > "  ₙ ₁ ₂ 𝕃 ℂ 𝔸 ⟦ ⟧ ⟨ ⟩ ❲❳"
  > "... but now on to the experiments."
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
