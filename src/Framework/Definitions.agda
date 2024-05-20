module Framework.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Data.Unit using (⊤; tt) public
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

-- open import Level using (suc; _⊔_)

{-
Some Atomic Data.
We have no assumptions on that data so its just a type.
-}
-- 𝔸 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔸 {ℓ} = Set ℓ
𝔸 : Set₁
𝔸 = Σ Set DecidableEquality

atoms : 𝔸 → Set
atoms = proj₁

{-
Variant Language.
A variant should represent atomic data in some way so its parameterized in atomic data.
-}
-- 𝕍 : ∀ {ℓ} → Set (suc ℓ)
-- 𝕍 {ℓ} = 𝔸 {ℓ} → Set ℓ
𝕍 : Set₂
𝕍 = 𝔸 → Set₁

{-
Annotation Language.
This can be names or propositional formulas or whatever you like to annotate artifacts with.
We have no assumptions on this kind of language (yet).
In the future, it might be interesting to dig deeper into 𝔽 and to explore its impact on a
language's expressiveness more deeply.
-}
-- 𝔽 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔽 {ℓ} = Set ℓ
𝔽 : Set₁
𝔽 = Set

{-
Feature Selection Language.
This is the semantic of an annotation language 𝔽. An instance of 𝕊 describes the
set of configurations for a feature language 𝔽.  Usually, each feature selection
language `S : 𝕊` has a some function `ConfigEvaluater F S Sel` which resolves an
expression of the annotation language `F : 𝔽` to a selection `Sel` interpreted
by a concrete language.
For example, a binary choice language may use `F → Bool` as the feature
selections language.
-}
𝕊 : Set₁
𝕊 = Set

𝕂 : Set₁
𝕂 = Set

{-
The set of expressions of a variability language.
An expression denotes a set of variants and hence, variant-like sub-terms
occur within an expression.
Such sub-terms describe variants of atomic data (i.e., some structure on atomic elements),
and hence expressions are parameterized in the type of this atomic data.
-}
-- 𝔼 : ∀ {ℓ} → Set (suc ℓ)
-- 𝔼 {ℓ} = 𝔸 {ℓ} → Set ℓ
𝔼 : Set₂
𝔼 = 𝔸 → Set₁

{-
Variability Construct.
A variability language is composed from a set of constructs (i.e., grammar rules).
Each construct may recursively contain further expressions (made up from constructs again).
Thus, constructs must know the overall set of expressions to include.
Moreover, constructs might directly host some atomic data (e.g., leaf nodes) and hence
they must know the atomic data type.
Moreover, constructs often denote variational expressions and hence require a language
for variability annotations 𝔽.
-}
-- ℂ : ∀ {ℓ} → Set (suc ℓ)
-- ℂ {ℓ} = 𝔼 {ℓ} → 𝔸 {ℓ} → Set ℓ
ℂ : Set₂
ℂ = 𝔼 → 𝔸 → Set₁
