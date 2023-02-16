{-# OPTIONS --sized-types #-}

module Test.UnitTest where

open import Size using (Size)
open import Function using (_∘_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Definitions using (Domain; VarLang; ConfLang; Semantics)
open import Translation.Translation

open import Test.Example using (Example; _called_)

open Data.List.Relation.Unary.All using ([]; _∷_) public
open Eq using (refl) public

{-
Unit tests are theorems on concrete examples
that the Agda type checker can figure out by itself.
-}
UnitTest : ∀ (Data : Set) → Set₁
UnitTest Data = Data → Set

ExamplesTest : ∀ (Data : Set) → Set₁
ExamplesTest Data = UnitTest (List (Example Data))

RunTest : ∀ {Data : Set}
  → UnitTest Data
  → Data
  → Set
RunTest utest dataset = utest dataset

ForExample : ∀ {Data : Set}
  → UnitTest Data
  → UnitTest (Example Data)
ForExample utest (e called _) = utest e

ForAll : ∀ {Data : Set}
  → UnitTest Data
  → UnitTest (List Data)
ForAll utest datasets = All utest datasets

ForAllExamples : ∀ {Data : Set}
  → UnitTest Data
  → ExamplesTest Data
ForAllExamples = ForAll ∘ ForExample

-- syntactic sugar for ForAllExamples that puts the example list in front
ForAllExamplesIn : ∀ {Data : Set}
  → List (Example Data)
  → UnitTest Data
  → Set
ForAllExamplesIn ex utest = ForAllExamples utest ex

test-translation : {i : Size} {A : Domain} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang}
  → (Translation L₁ L₂ C₁ C₂)
  → C₁
  → UnitTest (L₁ i A)
test-translation t c₁ e₁ =
  -- TODO: Can we somehow reuse our definition of _⊆-via_ here?
  let tr = translate t e₁
   in
      sem₁ t e₁ c₁ ≡ sem₂ t (expr tr) (conf tr c₁)

test-translation-fnoc∘conf≡id : {i : Size} {A : Domain} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang}
  → (Translation L₁ L₂ C₁ C₂)
  → C₁
  → UnitTest (L₁ i A)
test-translation-fnoc∘conf≡id t c₁ e₁ =
  let tr = translate t e₁
   in
      sem₁ t e₁ c₁ ≡ sem₁ t e₁ (fnoc tr (conf tr c₁))
