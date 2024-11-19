{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module Vatras.Main where

open import Level using (0ℓ; suc)

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Size using (∞)

open import Vatras.Show.Lines hiding (map)
open import Vatras.Show.Print

open import Vatras.Test.Example using (Example)
open import Vatras.Test.Experiment using (Experiment; ExperimentSetup; setup; run-setup)

open import Vatras.Test.Examples.CCC using (cccex-all)
open import Vatras.Test.Examples.OC using (optex-all)

open import Vatras.Test.Experiments.CCC-to-2CC
open import Vatras.Test.Experiments.OC-to-2CC

import Vatras.Test.Experiments.FST-Experiments as FSTs
open FSTs.Java.Calculator using (toy-calculator-experiment; ex-all)
open import Vatras.Test.Experiments.RoundTrip as RoundTrip using (round-trip)

{-|
A list of programs that we want to run.
Each program is implemented in terms of an Experiment.
Each experiment is run on each example from a list of examples (i.e., experiment inputs).
-}
experimentsToRun : List (ExperimentSetup (suc 0ℓ))
experimentsToRun =
  -- Run some example translations of option calculus to binary choice calculus
  setup exp-oc-to-bcc optex-all ∷
  -- Run some example configurations of feature structure trees.
  setup toy-calculator-experiment ex-all ∷
  -- Run the roundtrip demo.
  setup round-trip RoundTrip.examples ∷
  []

{-|
Implementation of what the main method should print.
-}
main_lines : Lines
main_lines = do
  linebreak
  > "It's dangerous to go alone! Take this unicode to see whether your terminal supports it:"
  > "  ₙ ₁ ₂ 𝕃 ℂ 𝔸 ⟦ ⟧ ⟨ ⟩ ❲❳"
  > "... but now on to the demo."
  linebreak
  linebreak
  overwrite-alignment-with
    Center
    (lines (map run-setup experimentsToRun))

open import IO using (IO; Main; putStrLn)

-- minor todo: use haskell to get width of current terminal
TERMINAL-WIDTH = 120

main : Main
main = IO.run (print TERMINAL-WIDTH main_lines)
