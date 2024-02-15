{-# OPTIONS --sized-types #-}

module Test.Experiments.OC-to-BCC where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
open import Data.Nat using (_+_)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; _++_; unlines; _==_)

open import Size using (Size; ∞)
open import Function using (id)
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Framework.Definitions using (ℂ)
open import Framework.Variants using (Rose; Artifact∈ₛRose; show-rose)

Feature = String
Variant = Rose ∞
mkArtifact = Artifact∈ₛRose

open import Lang.OC Feature as OCL renaming (Configuration to Conf-oc)
open import Lang.BCC Feature as BCCL
open OCL.Sem Variant mkArtifact renaming (⟦_⟧ to ⟦_⟧-oc)
open OCL.Show id
open BCCL.Sem Variant mkArtifact
open BCCL.Redundancy _==_
open BCCL.Pretty id

open import Translation.Lang.OC-to-BCC Feature using (compile; compile-configs)

open import Show.Lines
open import Util.Named
open import Show.Eval

open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

open import Test.UnitTest

OC→BCC-Test : UnitTest Conf-oc
OC→BCC-Test c = ForAllExamplesIn optex-all (test-translation WFOCL BCCL compile compile-configs c)

OC→BCC-Test-conffnoc : UnitTest Conf-oc
OC→BCC-Test-conffnoc c = ForAllExamplesIn optex-all (test-translation-fnoc∘conf≡id WFOCL BCCL compile-configs c)

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
get     exp-oc-to-bcc ex@(name ≔ oc) = do
  let --trans-result   = translate oc
      --bcc            = expr trans-result
      bcc            = compile oc

      bcc-simplified = eliminate-redundancy bcc
      pretty-bcc     = pretty bcc
      pretty-bcc-simplified = pretty bcc-simplified
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
    show-eval WFOCL (show-rose id) allyes-oc ex
    show-eval WFOCL (show-rose id) allno-oc  ex
  > "proven to be the same for the translated expression"
