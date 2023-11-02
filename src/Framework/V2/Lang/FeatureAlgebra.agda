module Framework.V2.Lang.FeatureAlgebra where

open import Data.Product using (proj₁; proj₂; _,_)
open import Data.List using (List) renaming (_∷_ to _．_)

open import Algebra.Structures using (IsMonoid)
open import Algebra.Core using (Op₂)
import Algebra.Definitions

open import Relation.Binary using (Rel; Reflexive; Transitive; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Level using (0ℓ; suc; _⊔_)

open import Framework.V2.Annotation.Name using (Name)

record FeaturePath (N : Set) (S : Set) : Set where
  constructor _∷_
  field
    name : Name N
    path : List S

record FeatureAlgebra {c} : Set (suc c) where
  open Algebra.Definitions using (Associative)
  open Eq.≡-Reasoning
  infixr 7 _⊕_

  field
    I : Set c
    _⊕_ : Op₂ I
    𝟘 : I

    monoid : IsMonoid _≡_ _⊕_ 𝟘

    -- Only the rightmost occurence of an introduction is effective in a sum,
    -- because it has been introduced first.
    -- This is, duplicates of i have no effect.
    distant-idempotence : ∀ (i₁ i₂ : I) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂
    direct-idempotence : ∀ (i : I) → i ⊕ i ≡ i

  open IsMonoid monoid

  -- introduction inclusion
  infix 6 _≤_
  _≤_ : Rel I c
  i₂ ≤ i₁ = i₂ ⊕ i₁ ≡ i₁

  ≤-refl : Reflexive _≤_
  ≤-refl {i} = direct-idempotence i

  ≤-trans : Transitive _≤_
  ≤-trans {i} {j} {k} i≤j j≤k =
    begin
      i ⊕ k
    ≡⟨ Eq.cong (i ⊕_) (Eq.sym j≤k) ⟩
      i ⊕ (j ⊕ k)
    ≡⟨ Eq.cong (λ x → i ⊕ x ⊕ k) (Eq.sym i≤j) ⟩
      i ⊕ ((i ⊕ j) ⊕ k)
    ≡⟨ Eq.sym (assoc i (i ⊕ j) k) ⟩
      (i ⊕ (i ⊕ j)) ⊕ k
    ≡⟨ Eq.cong (_⊕ k) (Eq.sym (assoc i i j)) ⟩
      ((i ⊕ i) ⊕ j) ⊕ k
    ≡⟨ Eq.cong (_⊕ k) (Eq.cong (_⊕ j) (direct-idempotence i)) ⟩
      (i ⊕ j) ⊕ k
    ≡⟨ Eq.cong (_⊕ k) i≤j ⟩
      j ⊕ k
    ≡⟨ j≤k ⟩
      k
    ∎

  least-element : ∀ i → 𝟘 ≤ i
  least-element = proj₁ identity

  upper-bound-l : ∀ i₂ i₁ → i₂ ≤ i₂ ⊕ i₁
  upper-bound-l i₂ i₁ =
    begin
      i₂ ⊕ (i₂ ⊕ i₁)
    ≡⟨ Eq.sym (assoc i₂ i₂ i₁) ⟩
      (i₂ ⊕ i₂) ⊕ i₁
    ≡⟨ Eq.cong (_⊕ i₁) (direct-idempotence i₂) ⟩
      i₂ ⊕ i₁
    ∎

  upper-bound-r : ∀ i₂ i₁ → i₁ ≤ i₂ ⊕ i₁
  upper-bound-r i₂ i₁ = distant-idempotence i₂ i₁
