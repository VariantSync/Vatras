open import Vatras.Framework.Definitions using (𝔽; NAT)
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

open FST.Impose F NAT

variant : Rose ∞ NAT
variant = 0 Rose.-< 0 Rose.-< [] >- ∷ [] >-

variantGenerator : VariantGenerator (Rose ∞) NAT 0
variantGenerator zero = variant

select-false : ∀ features → select (λ f → false) features ≡ []
select-false [] = refl
select-false (feature ∷ features) = select-false features

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

does-not-describe-variant : ¬ (Σ[ e ∈ SPL ] (⟦ e ⟧ ≅ variantGenerator))
does-not-describe-variant (e , variant⊆e , e⊆variant) with variant⊆e (λ f → false) | lemma e
does-not-describe-variant (e , variant⊆e , e⊆variant) | zero , e≡variant | a , e≡empty with Eq.trans (Eq.sym (proj₂ (Rose-injective e≡variant))) (proj₂ (Rose-injective e≡empty))
does-not-describe-variant (e , variant⊆e , e⊆variant) | zero , e≡variant | a , e≡empty | ()

FST-is-incomplete : Incomplete (Rose ∞) (FST.FSTL F)
FST-is-incomplete complete = does-not-describe-variant (Prod.map₂ (≅-sym) (complete variantGenerator))
