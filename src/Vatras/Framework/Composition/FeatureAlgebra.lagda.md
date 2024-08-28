# The Feature Algebra by Apel et al.

This module implements the feature algebra by

> _An algebraic foundation for automatic feature-based program synthesis_;
> Apel, Lengauer, Möller, Kästner;
> Science of Computer Programming; 2010

The algebra is an abstraction for static software composition, which means
that some data should be composed from a range of modules or components (before compilation
if our domain is programs).

```agda
module Vatras.Framework.Composition.FeatureAlgebra where

open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Algebra.Structures using (IsMonoid)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Associative)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence; IsPreorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Level using (suc; _⊔_)
```

The basic definition of a feature algebra consists of

- a set of introductions `I` (think of these as some kind of modules or components),
- a binary composition `sum : I → I → I` that composes two introductions (Definition 1),
- a neutral introduction `𝟘` which has no effect upon `sum`,

and must satisfy the following:

- `sum` must form a monoid with `𝟘`,
- the `distant-idempotence` law

For each definition, we document the corresponding definition, axiom, or lemma.
For further reasoning and documentation, we refer to the paper.

```
record FeatureAlgebra {c} (I : Set c) (sum : Op₂ I) (𝟘 : I) : Set (suc c) where
  open Eq.≡-Reasoning

  -- We define an alias for 'sum' so that we can add a fixity declaration.
  -- This allows us to write the laws like written in the paper.
  _⊕_ = sum
  infixr 7 _⊕_

  field
    -- Axiom 1 and 2
    monoid : IsMonoid _≡_ _⊕_ 𝟘

    {-|
    Axiom 3:
    Only the leftmost occurence of an introduction is effective in a sum,
    because it has been introduced first.
    This is, duplicates of i have no effect.
    -}
    distant-idempotence : ∀ (i₁ i₂ : I) → i₁ ⊕ i₂ ⊕ i₁ ≡ i₁ ⊕ i₂

  open IsMonoid monoid

  -- Lemma 1
  direct-idempotence : ∀ (i : I) → i ⊕ i ≡ i
  direct-idempotence i =
    begin
      i ⊕ i
    ≡⟨ Eq.cong (i ⊕_) (proj₁ identity i) ⟨
      i ⊕ 𝟘 ⊕ i
    ≡⟨ distant-idempotence i 𝟘 ⟩
      i ⊕ 𝟘
    ≡⟨ proj₂ identity i ⟩
      i
    ∎

  {-|
  Definition 2:
  Introduction Inclusion
  -}
  infix 6 _≤_
  _≤_ : Rel I c
  i₂ ≤ i₁ = i₁ ⊕ i₂ ≡ i₁

  -- Lemma 2
  ≤-refl : Reflexive _≤_
  ≤-refl {i} = direct-idempotence i

  -- Lemma 3
  ≤-trans : Transitive _≤_
  ≤-trans {i} {j} {k} i≤j j≤k =
    begin
      k ⊕ i
    ≡⟨ Eq.cong (_⊕ i) j≤k ⟨
      (k ⊕ j) ⊕ i
    ≡⟨ Eq.cong (λ x → (k ⊕ x) ⊕ i) i≤j ⟨
      (k ⊕ (j ⊕ i)) ⊕ i
    ≡⟨ assoc k (j ⊕ i) i ⟩
      k ⊕ ((j ⊕ i) ⊕ i)
    ≡⟨ Eq.cong (k ⊕_) (assoc j i i) ⟩
      k ⊕ (j ⊕ (i ⊕ i))
    ≡⟨ Eq.cong (k ⊕_) (Eq.cong (j ⊕_) (direct-idempotence i)) ⟩
      k ⊕ (j ⊕ i)
    ≡⟨ Eq.cong (k ⊕_) i≤j ⟩
      k ⊕ j
    ≡⟨ j≤k ⟩
      k
    ∎

  -- From the above, we can conclude that ≤ is a preorder.
  ≤-IsPreorder : IsPreorder _≡_ _≤_
  ≤-IsPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive = λ where refl → ≤-refl
    ; trans = ≤-trans
    }

  -- Lemma 4
  least-element : ∀ i → 𝟘 ≤ i
  least-element = proj₂ identity

  -- Lemma 5
  least-element-unique : ∀ i → i ≤ 𝟘 → i ≡ 𝟘
  least-element-unique i i≤𝟘 rewrite (proj₁ identity i) = i≤𝟘

  -- Lemma 6 (first part)
  upper-bound-l : ∀ i₂ i₁ → i₂ ≤ i₂ ⊕ i₁
  upper-bound-l i₂ i₁ =
    begin
      (i₂ ⊕ i₁) ⊕ i₂
    ≡⟨ assoc i₂ i₁ i₂ ⟩
      i₂ ⊕ (i₁ ⊕ i₂)
    ≡⟨ distant-idempotence i₂ i₁ ⟩
      i₂ ⊕ i₁
    ∎

  -- Lemma 6 (second and last part)
  upper-bound-r : ∀ i₂ i₁ → i₁ ≤ i₂ ⊕ i₁
  upper-bound-r i₂ i₁ =
    begin
      (i₂ ⊕ i₁) ⊕ i₁
    ≡⟨ assoc i₂ i₁ i₁ ⟩
      i₂ ⊕ (i₁ ⊕ i₁)
    ≡⟨ Eq.cong (i₂ ⊕_) (direct-idempotence i₁) ⟩
      i₂ ⊕ i₁
    ∎

  -- Lemma 7
  least-upper-bound : ∀ i i₂ i₁
    → i₁ ≤ i
    → i₂ ≤ i
      -----------
    → i₁ ⊕ i₂ ≤ i
  least-upper-bound i i₂ i₁ i₁≤i i₂≤i =
    begin
      i ⊕ (i₁ ⊕ i₂)
    ≡⟨ assoc i i₁ i₂ ⟨
      (i ⊕ i₁) ⊕ i₂
    ≡⟨ Eq.cong (_⊕ i₂) i₁≤i ⟩
      i ⊕ i₂
    ≡⟨ i₂≤i ⟩
      i
    ∎

  {-|
  Definition 3:
  Introduction Equivalence
  -}
  infix 6 _~_
  _~_ : Rel I c
  i₂ ~ i₁ = i₂ ≤ i₁ × i₁ ≤ i₂

  -- Introduction equivalence is reflexive (not mentioned in the paper).
  ~-refl : Reflexive _~_
  ~-refl = ≤-refl , ≤-refl

  -- Introduction equivalence is symmetric (not mentioned in the paper).
  ~-sym : Symmetric _~_
  ~-sym (fst , snd) = snd , fst

  -- Introduction equivalence is transitive (not mentioned in the paper).
  ~-trans : Transitive _~_
  ~-trans (i≤j , j≤i) (j≤k , k≤j) = ≤-trans i≤j j≤k , ≤-trans k≤j j≤i

  -- From the above we can conclude that introduction equivalence is an equivalence relation (not mentioned in the paper).
  ~-IsEquivalence : IsEquivalence _~_
  ~-IsEquivalence = record
    { refl  = ~-refl
    ; sym   = ~-sym
    ; trans = ~-trans
    }

  -- Helper for Lemma 8
  quasi-smaller : ∀ i₂ i₁ → i₂ ⊕ i₁ ≤ i₁ ⊕ i₂
  quasi-smaller i₂ i₁ =
    begin
      (i₁ ⊕ i₂) ⊕ (i₂ ⊕ i₁)
    ≡⟨ assoc (i₁ ⊕ i₂) i₂ i₁ ⟨
      ((i₁ ⊕ i₂) ⊕ i₂) ⊕ i₁
    ≡⟨ Eq.cong (_⊕ i₁) (assoc i₁ i₂ i₂) ⟩
      (i₁ ⊕ (i₂ ⊕ i₂)) ⊕ i₁
    ≡⟨ Eq.cong (_⊕ i₁) (Eq.cong (i₁ ⊕_) (direct-idempotence i₂)) ⟩
      (i₁ ⊕ i₂) ⊕ i₁
    ≡⟨ assoc i₁ i₂ i₁ ⟩
      i₁ ⊕ (i₂ ⊕ i₁)
    ≡⟨ distant-idempotence i₁ i₂ ⟩
      i₁ ⊕ i₂
    ∎

  {-
  Lemma 8:
  Introduction sum is commutative with respec to introduction equivalence.
  This means that on both sides, we have introductions that both "contain" the same introduction
  but maybe in a different order (so the results are not propositionally equal).
  Note that in general, introduction sum is not commutative with respect to proposition equality
  (i.e., the syntax of the actual introduction type).
  -}
  quasi-commutativity : ∀ i₂ i₁ → i₂ ⊕ i₁ ~ i₁ ⊕ i₂
  quasi-commutativity i₂ i₁ = quasi-smaller i₂ i₁ , quasi-smaller i₁ i₂
```
