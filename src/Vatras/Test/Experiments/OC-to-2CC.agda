module Vatras.Test.Experiments.OC-to-2CC where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
open import Data.Nat using (_+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String as String using (String; _++_; unlines; _≟_)

open import Size using (Size; ∞)
open import Function using (id)
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Vatras.Framework.Definitions using (ℂ)
open import Vatras.Framework.Variants using (Rose; show-rose)

Feature = String

open import Vatras.Lang.All
open OC using (WFOC; WFOCL)
open import Vatras.Lang.OC.Util using (allyes-oc; allno-oc)
open import Vatras.Lang.OC.Show id using (show-wfoc)
open 2CC using (2CCL)
open import Vatras.Translation.Lang.2CC.Redundancy Feature _≟_
open import Vatras.Lang.2CC.Show id using (pretty)

open import Vatras.Translation.Lang.OC-to-2CC Feature using (compile; compile-configs)

open import Vatras.Show.Lines
open import Vatras.Util.Named
open import Vatras.Show.Eval

open import Vatras.Test.Experiment
open import Vatras.Test.Example
open import Vatras.Test.Examples.OC

open import Vatras.Test.UnitTest

OC→2CC-Test : UnitTest (OC.Configuration Feature)
OC→2CC-Test c = ForAllExamplesIn optex-all (test-translation (WFOCL Feature) (2CCL Feature) compile compile-configs c)

OC→2CC-Test-conffnoc : UnitTest (OC.Configuration Feature)
OC→2CC-Test-conffnoc c = ForAllExamplesIn optex-all (test-translation-fnoc∘conf≡id (WFOCL Feature) (2CCL Feature) compile-configs c)

-- agda computes this value automatically!
-- Better: When we add a new example to optex-all, the test wont compile before we adapted it. So we can never forget to test it.
OC→2CC-Test-allyes : RunTest OC→2CC-Test (get allyes-oc)
OC→2CC-Test-allyes = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→2CC-Test-allno : RunTest OC→2CC-Test (get allno-oc)
OC→2CC-Test-allno = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→2CC-Test-conffnoc-allyes : RunTest OC→2CC-Test-conffnoc (get allyes-oc)
OC→2CC-Test-conffnoc-allyes = refl ∷ refl ∷ refl ∷ refl ∷ []

OC→2CC-Test-conffnoc-allno : RunTest OC→2CC-Test-conffnoc (get allno-oc)
OC→2CC-Test-conffnoc-allno = refl ∷ refl ∷ refl ∷ refl ∷ []

-- Translate an option calculus expression.
-- Then configure it with an all-yes and an all-no config and print the resulting variants.
exp-oc-to-bcc : Experiment (WFOC Feature ∞ (String , String._≟_))
getName exp-oc-to-bcc = "Translate OC to 2CC"
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
    show-eval (WFOCL Feature) (show-rose id) allyes-oc ex
    show-eval (WFOCL Feature) (show-rose id) allno-oc  ex
  > "proven to be the same for the translated expression"
