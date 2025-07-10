{-|
This module renames variables in Prop expressions.

The idea of this translation is to apply a renaming function `f : F₁ → F₂` to
all elements of `F₁` in the datastructure `Prop F₁` to obtain a new datastructure
`Prop F₂`. To prove preservation of the semantics, we also require a left inverse
`f⁻¹ : D₂ → D₁` of `f` as a proof that `f` is injective. This precondition is
necessary because a non-injective rename could reduce the number of variables.
-}
module Vatras.Data.Prop.Rename where

import Data.Bool as Bool
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)

open import Vatras.Data.Prop

rename : {F₁ F₂ : Set} → (F₁ → F₂) → Prop F₁ → Prop F₂
rename f true = true
rename f false = false
rename f (var v) = var (f v)
rename f (¬ p) = ¬ (rename f p)
rename f (p ∧ q) = rename f p ∧ rename f q

rename-spec
  : {F₁ F₂ : Set}
  → (f : F₁ → F₂)
  → (p : Prop F₁)
  → (c : Assignment F₂)
  → eval (rename f p) c ≡ eval p (c ∘ f)
rename-spec f true c = refl
rename-spec f false c = refl
rename-spec f (var v) c = refl
rename-spec f (¬ p) c = Eq.cong Bool.not (rename-spec f p c)
rename-spec f (p ∧ q) c = Eq.cong₂ Bool._∧_ (rename-spec f p c) (rename-spec f q c)

rename-preserves
  : {F₁ F₂ : Set}
  → (f : F₁ → F₂)
  → (f⁻¹ : F₂ → F₁)
  → f⁻¹ ∘ f ≗ id
  → (p : Prop F₁)
  → (c : Assignment F₁)
  → eval (rename f p) (c ∘ f⁻¹) ≡ eval p c
rename-preserves f f⁻¹ f∘f⁻¹≗id true c = refl
rename-preserves f f⁻¹ f∘f⁻¹≗id false c = refl
rename-preserves f f⁻¹ f∘f⁻¹≗id (var v) c = Eq.cong c (f∘f⁻¹≗id v)
rename-preserves f f⁻¹ f∘f⁻¹≗id (¬ p) c = Eq.cong Bool.not (rename-preserves f f⁻¹ f∘f⁻¹≗id p c)
rename-preserves f f⁻¹ f∘f⁻¹≗id (p ∧ q) c = Eq.cong₂ Bool._∧_ (rename-preserves f f⁻¹ f∘f⁻¹≗id p c) (rename-preserves f f⁻¹ f∘f⁻¹≗id q c)
