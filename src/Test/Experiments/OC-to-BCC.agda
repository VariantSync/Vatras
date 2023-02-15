{-# OPTIONS --sized-types #-}

module Test.Experiments.OC-to-BCC where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
open import Data.Nat using (_+_)
open import Data.String using (String; _++_; unlines)

open import Size using (Size; ∞)
open import Function using (id)
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

import Lang.OC
import Lang.BCC

open Lang.OC renaming (⟦_⟧ to ⟦_⟧-oc; Configuration to Conf-oc)
open Lang.BCC renaming (⟦_⟧ to ⟦_⟧-bcc; Configuration to Conf-bcc)

open import Translation.Translation using (expr; ConfLang)
open import Translation.OC-to-BCC using (translate; OC→BCC)

open import Show.Lines
open import Util.Named
open import Show.Eval

open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

open import Test.UnitTest

OC→BCC-Test : UnitTest Conf-oc
OC→BCC-Test c = ForAllExamplesIn optex-all (test-translation OC→BCC c)

OC→BCC-Test-conffnoc : UnitTest Conf-oc
OC→BCC-Test-conffnoc c = ForAllExamplesIn optex-all (test-translation-fnoc∘conf≡id OC→BCC c)

-- agda computes this value automatically!
-- Better: When we add a new example to optex-all, the test wont compile before we adapted it. So we can never forget to test it.
OC→BCC-Test-allyes : RunTest OC→BCC-Test (get allyes-oc)
OC→BCC-Test-allyes = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→BCC-Test-allno : RunTest OC→BCC-Test (get allno-oc)
OC→BCC-Test-allno = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→BCC-Test-conffnoc-allyes : RunTest OC→BCC-Test-conffnoc (get allyes-oc)
OC→BCC-Test-conffnoc-allyes = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→BCC-Test-conffnoc-allno : RunTest OC→BCC-Test-conffnoc (get allno-oc)
OC→BCC-Test-conffnoc-allno = refl ∷ refl ∷ refl ∷ refl ∷ []

-- Translate an option calculus expression.
-- Then configure it with an all-yes and an all-no config and print the resulting variants.
exp-oc-to-bcc : Experiment (WFOC ∞ String)
getName exp-oc-to-bcc = "Translate OC to BCC"
get     exp-oc-to-bcc ex@(name example: oc) = do
  let trans-result   = translate oc
      bcc            = expr trans-result
      bcc-simplified = eliminate-redundancy bcc
      pretty-bcc     = Lang.BCC.pretty bcc
      pretty-bcc-simplified = Lang.BCC.pretty bcc-simplified
  [ Center ]> show-wfoc oc
  linebreak
  [ Center ]> "│"
  [ Center ]> "          │ translate"
  [ Center ]> "↓"
  linebreak
  overwrite-alignment-with Center
    (boxed (6 + width pretty-bcc) "" pretty-bcc)
  linebreak
  [ Center ]> "│"
  [ Center ]> "                     │ eliminate redundancy"
  [ Center ]> "↓"
  linebreak
  overwrite-alignment-with Center
    (boxed (6 + width pretty-bcc-simplified) "" pretty-bcc-simplified)
  linebreak
  > "Variants:"
  indent 2 do
    show-eval-str ⟦_⟧-oc allyes-oc ex
    show-eval-str ⟦_⟧-oc allno-oc  ex
  > "proven to be the same for the translated expression"
