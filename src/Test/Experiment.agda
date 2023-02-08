module Test.Experiment where

open import Data.Nat using (_+_)
open import Data.List using (List; map)
open import Data.String using (String; _++_; length; replicate)

open import Show.Lines

open import Test.Example

record Experiment (A : Set) : Set₁ where
  field
    name : String
    run : Example A → Lines
open Experiment public

runOn : ∀ {A : Set} → Experiment A → Example A → Lines
runOn experiment example =
  let title = "───────────────── Example: " ++ name example ++ " ─────────────────"
  in do
    linebreak
    >      "┌" ++ title
    prefix "│" (indent 2 (run experiment example))
    >      "└" ++ replicate (length title) '─'
    linebreak

runAll : {A : Set} → Experiment A → List (Example A) → Lines
runAll experiment examples = do
  headline "BEGIN Experiment" (name experiment)
  indent 2 (lines (map (runOn experiment) examples))
  headline " END Experiment " (name experiment)
