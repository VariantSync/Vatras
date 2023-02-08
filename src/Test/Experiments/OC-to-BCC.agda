{-# OPTIONS --sized-types #-}

module Test.Experiments.OC-to-BCC where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
open import Data.String using (String; _++_; unlines)

open import Size using (∞)
open import Function using (id)
open import Level using (0ℓ)

open import Lang.OC
open import Lang.BCC
open import Translation.Translation using (expr)
open import Translation.OC-to-BCC using (translate)

open import Show.Lines

open import Test.Test
open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

test-variant-equality :
    (confName : String)
  → Lang.OC.Configuration
  → Lang.BCC.Configuration
  → (wfocName : String)
  → (bccName : String)
  → WFOC ∞ String
  → BCC ∞ String
  → Lines
test-variant-equality = test-confs id Lang.OC.⟦_⟧ Lang.BCC.⟦_⟧ Data.String._≟_

-- Configure an option calculus expression with an all-yes and an all-no config and print the resulting variants.
exp-oc-to-bcc : Experiment (WFOC ∞ String)
name exp-oc-to-bcc = "Translate OC expression to BCC"
run  exp-oc-to-bcc (name example: oc) = do
  let trans-result = translate oc
      bcc = expr trans-result
  > "𝑎: " ++ show-wfoc oc
  > "  ↓  "
  > "𝑏: " ++ Lang.BCC.show bcc
  linebreak
  test-variant-equality "all-yes" (λ _ → true)  (λ _ → true)  "𝑎" "𝑏" oc bcc
  test-variant-equality "all-no"  (λ _ → false) (λ _ → false) "𝑎" "𝑏" oc bcc
