module Test.Experiment where

open import Data.Nat using (ℕ; _+_; _∸_)
open import Data.List using (List; map)
open import Data.String using (String; _++_; length; replicate)

open import Show.Lines

open import Test.Example
open import Util.Named

EXPERIMENT-BOX-WIDTH : ℕ
EXPERIMENT-BOX-WIDTH = 100

EXAMPLE-BOX-WIDTH : ℕ
EXAMPLE-BOX-WIDTH = EXPERIMENT-BOX-WIDTH ∸ 6

-- An experiment has a name and consists of a function "Example A → Lines" that runs the experment on a given example.
Experiment : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Experiment A = Named (Example A → Lines)

run : ∀ {ℓ} {A : Set ℓ} → Experiment A → Example A → Lines
run = get

runOn : ∀ {A : Set} → Experiment A → Example A → Lines
runOn experiment example = do
  linebreak
  boxed
    EXAMPLE-BOX-WIDTH
    ("Example: " ++ getName example)
    (do
      linebreak
      run experiment example
      linebreak
    )
  linebreak

runAll : {A : Set} → Experiment A → List (Example A) → Lines
runAll experiment examples = do
  boxed
    EXPERIMENT-BOX-WIDTH
    ("Experiment: " ++ (getName experiment))
    (lines (map (runOn experiment) examples))
  linebreak
