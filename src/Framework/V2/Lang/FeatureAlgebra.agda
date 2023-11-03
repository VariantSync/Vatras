module Framework.V2.Lang.FeatureAlgebra where

open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Algebra.Structures using (IsMonoid)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Associative)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence; IsPreorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Level using (suc; _⊔_)

record FeatureAlgebra {c} (I : Set c) (sum : Op₂ I) (𝟘 : I) : Set (suc c) where
  open Eq.≡-Reasoning

  _⊕_ = sum
  infixr 7 _⊕_

  field
    monoid : IsMonoid _≡_ _⊕_ 𝟘

    -- Only the rightmost occurence of an introduction is effective in a sum,
    -- because it has been introduced first.
    -- This is, duplicates of i have no effect.
    distant-idempotence : ∀ (i₁ i₂ : I) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂

  open IsMonoid monoid

  direct-idempotence : ∀ (i : I) → i ⊕ i ≡ i
  direct-idempotence i =
    begin
      i ⊕ i
    ≡˘⟨ Eq.cong (i ⊕_) (proj₁ identity i) ⟩
      i ⊕ 𝟘 ⊕ i
    ≡⟨ distant-idempotence 𝟘 i ⟩
      𝟘 ⊕ i
    ≡⟨ proj₁ identity i ⟩
      i
    ∎

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
    ≡˘⟨ Eq.cong (i ⊕_) j≤k ⟩
      i ⊕ (j ⊕ k)
    ≡˘⟨ Eq.cong (λ x → i ⊕ x ⊕ k) i≤j ⟩
      i ⊕ ((i ⊕ j) ⊕ k)
    ≡˘⟨ assoc i (i ⊕ j) k ⟩
      (i ⊕ (i ⊕ j)) ⊕ k
    ≡˘⟨ Eq.cong (_⊕ k) (assoc i i j) ⟩
      ((i ⊕ i) ⊕ j) ⊕ k
    ≡⟨ Eq.cong (_⊕ k) (Eq.cong (_⊕ j) (direct-idempotence i)) ⟩
      (i ⊕ j) ⊕ k
    ≡⟨ Eq.cong (_⊕ k) i≤j ⟩
      j ⊕ k
    ≡⟨ j≤k ⟩
      k
    ∎

  ≤-IsPreorder : IsPreorder _≡_ _≤_
  ≤-IsPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive = λ where refl → ≤-refl
    ; trans = ≤-trans
    }

  least-element : ∀ i → 𝟘 ≤ i
  least-element = proj₁ identity

  least-element-unique : ∀ i → i ≤ 𝟘 → i ≡ 𝟘
  least-element-unique i i≤𝟘 rewrite (proj₂ identity i) = i≤𝟘

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

  least-upper-bound : ∀ i i₂ i₁
    → i₁ ≤ i
    → i₂ ≤ i
      -----------
    → i₁ ⊕ i₂ ≤ i
  least-upper-bound i i₂ i₁ i₁≤i i₂≤i =
    begin
      (i₁ ⊕ i₂) ⊕ i
    ≡⟨ assoc i₁ i₂ i ⟩
      i₁ ⊕ (i₂ ⊕ i)
    ≡⟨ Eq.cong (i₁ ⊕_) i₂≤i ⟩
      i₁ ⊕ i
    ≡⟨ i₁≤i ⟩
      i
    ∎

  -- introduction equivalence
  infix 6 _~_
  _~_ : Rel I c
  i₂ ~ i₁ = i₂ ≤ i₁ × i₁ ≤ i₂

  ~-refl : Reflexive _~_
  ~-refl = ≤-refl , ≤-refl

  ~-sym : Symmetric _~_
  ~-sym (fst , snd) = snd , fst

  ~-trans : Transitive _~_
  ~-trans (i≤j , j≤i) (j≤k , k≤j) = ≤-trans i≤j j≤k , ≤-trans k≤j j≤i

  ~-IsEquivalence : IsEquivalence _~_
  ~-IsEquivalence = record
    { refl  = ~-refl
    ; sym   = ~-sym
    ; trans = ~-trans
    }

  quasi-smaller : ∀ i₂ i₁ → i₂ ⊕ i₁ ≤ i₁ ⊕ i₂
  quasi-smaller i₂ i₁ =
    begin
      (i₂ ⊕ i₁) ⊕ i₁ ⊕ i₂
    ≡⟨⟩
      (i₂ ⊕ i₁) ⊕ (i₁ ⊕ i₂)
    ≡˘⟨ assoc (i₂ ⊕ i₁) i₁ i₂ ⟩
      ((i₂ ⊕ i₁) ⊕ i₁) ⊕ i₂
    ≡⟨ Eq.cong (_⊕ i₂) (assoc i₂ i₁ i₁) ⟩
      (i₂ ⊕ (i₁ ⊕ i₁)) ⊕ i₂
    ≡⟨ Eq.cong (_⊕ i₂) (Eq.cong (i₂ ⊕_) (direct-idempotence i₁)) ⟩
      (i₂ ⊕ i₁) ⊕ i₂
    ≡⟨ assoc i₂ i₁ i₂ ⟩
      i₂ ⊕ i₁ ⊕ i₂
    ≡⟨ distant-idempotence i₁ i₂ ⟩
      i₁ ⊕ i₂
    ∎

  quasi-commutativity : ∀ i₂ i₁ → i₂ ⊕ i₁ ~ i₁ ⊕ i₂
  quasi-commutativity i₂ i₁ = quasi-smaller i₂ i₁ , quasi-smaller i₁ i₂
