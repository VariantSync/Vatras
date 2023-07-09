{-# OPTIONS --sized-types #-}

module Test.UnitTest where


open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Function using (_∘_)
open import Level using (0ℓ; _⊔_; suc)
open import Size using (Size)

open import Framework.Definitions
open import Translation.Translation

open import Test.Example using (Example; _called_)

open Data.List.Relation.Unary.All using ([]; _∷_) public
open Eq using (refl) public

{-
Unit tests are theorems on concrete examples
that the Agda type checker can figure out by itself.
-}
UnitTest : ∀ {ℓ} (Data : Set ℓ) → Set (suc 0ℓ ⊔ ℓ)
UnitTest Data = Data → Set

ExamplesTest : ∀ {ℓ} (Data : Set ℓ) → Set (suc 0ℓ ⊔ ℓ)
ExamplesTest Data = UnitTest (List (Example Data))

RunTest : ∀ {ℓ} {Data : Set ℓ}
  → UnitTest Data
  → Data
  → Set
RunTest utest dataset = utest dataset

ForExample : ∀ {ℓ} {Data : Set ℓ}
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

test-translation : ∀ {L₁ L₂ : VariabilityLanguage} {A i}
  → (Translation L₁ L₂)
  → configuration L₁
  → UnitTest (expression L₁ i A)
test-translation {L₁} {L₂} {A} translate c₁ e₁ =
  -- TODO: Can we somehow reuse our definition of _⊆-via_ here?
  let tr : TranslationResult A L₁ L₂
      tr = translate e₁
      e₂ = expr tr
      ⟦_⟧₁ = semantics L₁
      ⟦_⟧₂ = semantics L₂
   in
      ⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₂ ⟧₂ (conf tr c₁)

test-translation-fnoc∘conf≡id : ∀ {L₁ L₂ : VariabilityLanguage} {A i}
  → (Translation L₁ L₂)
  → configuration L₁
  → UnitTest (expression L₁ i A)
test-translation-fnoc∘conf≡id {L₁} {_} t c₁ e₁ =
  let tr = t e₁
      ⟦_⟧₁ = semantics L₁
   in
      ⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₁ ⟧₁ (fnoc tr (conf tr c₁))
