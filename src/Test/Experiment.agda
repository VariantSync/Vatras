module Test.Experiment where

open import Data.List using (List; map)
open import Data.Nat using (ℕ; _+_; _∸_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; _++_; length; replicate)
open import Level using (suc)

open import Show.Lines hiding (map)

open import Test.Example
open import Util.Named

EXPERIMENT-BOX-WIDTH : ℕ
EXPERIMENT-BOX-WIDTH = 100

EXAMPLE-BOX-WIDTH : ℕ
EXAMPLE-BOX-WIDTH = EXPERIMENT-BOX-WIDTH ∸ 6

-- An experiment has a name and consists of a function "Example A → Lines" that runs the experment on a given example.
Experiment : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Experiment A = Named (Example A → Lines)

-- An Experiment paired with a list of input examples to run the experiment on.
ExperimentSetup : ∀ ℓ → Set (suc ℓ)
ExperimentSetup ℓ = Σ[ A ∈ Set ℓ ] (Experiment A × List (Example A))

-- This functions creates an ExperimentSetup from an experiment and its list of inputs.
-- (This basically constitutes a smart constructor avoiding the need to explicitly state
-- the type of the underlying input data.)
setup : ∀ {ℓ} {A : Set ℓ} → Experiment A → List (Example A) → ExperimentSetup ℓ
setup {ℓ} {A} program inputs = A , program , inputs

run-experiment : ∀ {ℓ} {A : Set ℓ} → Experiment A → Example A → Lines
run-experiment experiment example = do
  linebreak
  boxed
    EXAMPLE-BOX-WIDTH
    ("Example: " ++ getName example)
    (do
      linebreak
      get experiment example
      linebreak
    )
  linebreak

run-setup : ∀ {ℓ} → ExperimentSetup ℓ → Lines
run-setup (_ , experiment , examples) = do
  boxed
    EXPERIMENT-BOX-WIDTH
    ("Experiment: " ++ (getName experiment))
    (lines (map (run-experiment experiment) examples))
  linebreak
