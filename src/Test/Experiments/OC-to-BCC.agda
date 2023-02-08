{-# OPTIONS --sized-types #-}

module Test.Experiments.OC-to-BCC where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
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

open import Translation.Translation using (expr)
open import Translation.OC-to-BCC using (translate)

open import Show.Lines

open import Test.Test
open import Test.Experiment
open import Test.Example
open import Test.Examples.OC

test-variant-equality :
    (confName : String)
  → Conf-oc
  → Conf-bcc
  → (wfocName : String)
  → (bccName : String)
  → WFOC ∞ String
  → BCC ∞ String
  → Lines
test-variant-equality = test-confs id ⟦_⟧-oc ⟦_⟧-bcc Data.String._≟_

-- TODO: Extract small unit test framework and apply it to all our examples
UnitTest :
    (cₒ : Conf-oc)
  → (c₂ : Conf-bcc)
  → Example (WFOC ∞ String)
  → Set
UnitTest cₒ c₂ (_ example: e) = ⟦ e ⟧-oc cₒ ≡ ⟦ expr (translate e) ⟧-bcc c₂

all-oc : Bool → Conf-oc
all-oc b _ = b

all-bcc : Bool → Conf-bcc
all-bcc b _ = b

test-sandwich : UnitTest (all-oc true) (all-bcc true) optex-sandwich
test-sandwich = refl

open import Data.List.Relation.Unary.All using (All; []; _∷_)

-- agda could compute this value automatically!
-- Better: When we add a new example to optex-all, the test wont compile before we adapted it. So we can never forget to test it.
test-all : All (UnitTest (all-oc true) (all-bcc true)) optex-all
test-all = refl ∷ (refl ∷ (refl ∷ []))

-- Configure an option calculus expression with an all-yes and an all-no config and print the resulting variants.
exp-oc-to-bcc : Experiment (WFOC ∞ String)
name exp-oc-to-bcc = "Translate OC to BCC"
run  exp-oc-to-bcc (name example: oc) = do
  let oc-name  = "oc "
      bcc-name = "bcc"
      trans-result = translate oc
      bcc = expr trans-result
  [ Center ]> show-wfoc oc
  [ Center ]> "↓"
  [ Center ]> Lang.BCC.show bcc
  linebreak
  test-variant-equality "all-yes" (all-oc true)  (all-bcc true)  oc-name bcc-name oc bcc
  test-variant-equality "all-no"  (all-oc false) (all-bcc false) oc-name bcc-name oc bcc
