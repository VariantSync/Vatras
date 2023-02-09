module Test.Experiment where

open import Data.Nat using (ℕ; _+_; _∸_)
open import Data.List using (List; map)
open import Data.String using (String; _++_; length; replicate)

open import Show.Lines

open import Test.Example

EXPERIMENT-BOX-WIDTH : ℕ
EXPERIMENT-BOX-WIDTH = 100

EXAMPLE-BOX-WIDTH : ℕ
EXAMPLE-BOX-WIDTH = EXPERIMENT-BOX-WIDTH ∸ 6

record Experiment (A : Set) : Set₁ where
  field
    name : String
    run : Example A → Lines
open Experiment public

runOn : ∀ {A : Set} → Experiment A → Example A → Lines
runOn experiment example = do
  linebreak
  boxed
    EXAMPLE-BOX-WIDTH
    ("Example: " ++ name example)
    (run experiment example)
  linebreak

runAll : {A : Set} → Experiment A → List (Example A) → Lines
runAll experiment examples = do
  boxed
    EXPERIMENT-BOX-WIDTH
    ("Experiment: " ++ (name experiment))
    (lines (map (runOn experiment) examples))
  linebreak
