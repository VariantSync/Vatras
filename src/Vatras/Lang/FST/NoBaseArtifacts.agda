{-|
Proof that feature structure trees do not contain a base artifact.
In other words: Every feature structure tree contains a variant that has no children.
Hence, feature structure trees are incomplete
(they cannot encode a variant set that does not contain a variant without children).
-}

open import Vatras.Framework.Definitions using (𝔽; NAT')
module Vatras.Lang.FST.NoBaseArtifacts {F : 𝔽} where

open import Data.Bool using (true; false)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Prod using (_,_; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Size using (∞)

open import Vatras.Data.EqIndexedSet using (_≅_; ≅-sym)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.VariantGenerator using (VariantGenerator)
open import Vatras.Framework.Properties.Completeness using (Incomplete)
import Vatras.Lang.FST as FST

open FST.Impose F NAT'

{-|
A variant that has at least one child.
-}
variant : Rose ∞ NAT'
variant = 0 Rose.-< 0 Rose.-< [] >- ∷ [] >-

{-|
A variant set that does not contain the variant that has no children.
-}
variantGenerator : VariantGenerator (Rose ∞) NAT' 0
variantGenerator zero = variant

{-|
The configuration `λ f → false` results in no selected features.
-}
select-false : ∀ features → select (λ f → false) features ≡ []
select-false [] = refl
select-false (feature ∷ features) = select-false features

{-|
Every feature structure tree contains a variant without children.
-}
lemma : ∀ (e : SPL) → Σ[ a ∈ ℕ ] ⟦ e ⟧ (λ f → false) ≡ a Rose.-< [] >-
lemma (a ◀ features) = a , (
  begin
    ⟦ a ◀ features ⟧ (λ f → false)
  ≡⟨⟩
    a Rose.-< forget-uniqueness (⊛-all (select (λ f → false) features)) >-
  ≡⟨ Eq.cong (λ x → a Rose.-< forget-uniqueness (⊛-all x) >-) (select-false features) ⟩
    a Rose.-< forget-uniqueness (⊛-all []) >-
  ≡⟨⟩
    a Rose.-< [] >-
  ∎)
  where
  open Eq.≡-Reasoning

{-|
The variant set `variantGenerator` cannot be expressed by a feature structure tree.
-}
does-not-describe-variant : ¬ (Σ[ e ∈ SPL ] (⟦ e ⟧ ≅ variantGenerator))
does-not-describe-variant (e , variant⊆e , e⊆variant) with variant⊆e (λ f → false) | lemma e
does-not-describe-variant (e , variant⊆e , e⊆variant) | zero , e≡variant | a , e≡empty with Eq.trans (Eq.sym (proj₂ (Rose-injective e≡variant))) (proj₂ (Rose-injective e≡empty))
does-not-describe-variant (e , variant⊆e , e⊆variant) | zero , e≡variant | a , e≡empty | ()

{-|
Due to `does-not-describe-variant`, feature structure trees are incomplete.
-}
FST-is-incomplete : Incomplete (Rose ∞) (FST.FSTL F)
FST-is-incomplete complete = does-not-describe-variant (Prod.map₂ (≅-sym) (complete variantGenerator))
