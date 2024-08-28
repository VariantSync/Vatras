module Vatras.Test.UnitTest where

open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Function using (_∘_)
open import Level using (0ℓ; _⊔_; suc)
open import Size using (Size)

open import Vatras.Framework.Definitions
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Relation.Function using (_⇒ₚ_; _⇔_; to; from)

open import Vatras.Test.Example using (Example; _called_)

open Data.List.Relation.Unary.All using ([]; _∷_) public
open Eq using (refl) public

{-
Unit tests are theorems on concrete examples
that the Agda type checker can figure out by itself.
-}
UnitTest : ∀ {ℓ₁ ℓ₂} (Data : Set ℓ₂) → Set (suc ℓ₁ ⊔ ℓ₂)
UnitTest {ℓ₁} Data = Data → Set ℓ₁

ExamplesTest : ∀ {ℓ₁ ℓ₂} (Data : Set ℓ₂) → Set (suc ℓ₁ ⊔ ℓ₂)
ExamplesTest {ℓ₁} Data = UnitTest {ℓ₁} (List (Example Data))

RunTest : ∀ {ℓ₁ ℓ₂} {Data : Set ℓ₂}
  → UnitTest {ℓ₁} Data
  → Data
  → Set ℓ₁
RunTest utest dataset = utest dataset

ForExample : ∀ {ℓ₁ ℓ₂} {Data : Set ℓ₂}
  → UnitTest {ℓ₁} Data
  → UnitTest {ℓ₁} (Example Data)
ForExample utest (e called _) = utest e

ForAll : ∀ {ℓ₁ ℓ₂} {Data : Set ℓ₂}
  → UnitTest {ℓ₁} Data
  → UnitTest {ℓ₁ ⊔ ℓ₂} (List Data)
ForAll utest datasets = All utest datasets

ForAllExamples : ∀ {ℓ₁ ℓ₂} {Data : Set ℓ₂}
  → UnitTest {ℓ₁} Data
  → ExamplesTest {ℓ₁ ⊔ ℓ₂} Data
ForAllExamples = ForAll ∘ ForExample

-- syntactic sugar for ForAllExamples that puts the example list in front
ForAllExamplesIn : ∀ {ℓ₁ ℓ₂} {Data : Set ℓ₂}
  → List (Example Data)
  → UnitTest {ℓ₁} Data
  → Set (ℓ₁ ⊔ ℓ₂)
ForAllExamplesIn ex utest = ForAllExamples utest ex

test-translation : ∀ {V A}
  → (L₁ L₂ : VariabilityLanguage V)
  → (Expression L₁ A → Expression L₂ A)
  → Config L₁ ⇔ Config L₂
  → Config L₁
  → UnitTest (Expression L₁ A)
test-translation L₁ L₂ translate t c₁ e₁ =
  -- TODO: Can we somehow reuse our definition of _⊆-via_ here?
  ⟦ e₁ ⟧₁ c₁ ≡ ⟦ translate e₁ ⟧₂ (to t c₁)
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂

test-translation-fnoc∘conf≡id : ∀ {V A}
  → (L₁ L₂ : VariabilityLanguage V)
  → Config L₁ ⇔ Config L₂
  → Config L₁
  → UnitTest (Expression L₁ A)
test-translation-fnoc∘conf≡id L₁ _ t c₁ e₁ =
  ⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₁ ⟧₁ (from t (to t c₁))
  where
    ⟦_⟧₁ = Semantics L₁
