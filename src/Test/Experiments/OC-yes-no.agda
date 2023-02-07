{-# OPTIONS --sized-types --guardedness #-}

module Test.Experiments.OC-yes-no where

open import Data.Bool using (true; false)
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_; unlines)
open import Size using (∞)
open import IO using (putStrLn; _>>_)

open import Lang.OC
open import SemanticDomain using (showVariant)

open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

-- Configure an option calculus expression with an all-yes and an all-no config and print the resulting variants.
exp-run-allyes-and-allno : Experiment (WFOC ∞ String)
name exp-run-allyes-and-allno = "Configure OC expression with all-yes and all-no configuration"
run  exp-run-allyes-and-allno (name example: e) = do
  putStrLn (name ++ " = " ++ show-wfoc e)
  putStrLn ("[[" ++ name ++ "]] (λ x → true)  = " ++ showVariant (⟦ e ⟧ (λ _ → true) ))
  putStrLn ("[[" ++ name ++ "]] (λ x → false) = " ++ showVariant (⟦ e ⟧ (λ _ → false)))

