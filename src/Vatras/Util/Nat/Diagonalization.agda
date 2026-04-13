module Vatras.Util.Nat.Diagonalization where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; []; _∷_; _∷ʳ_; _++_; replicate)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≤?_)
import Data.Nat.Properties as ℕ
open import Data.Product as Product using (_×_; _,_; uncurry; Σ-syntax)
open import Function using (_∘_; id; const)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)

import Vatras.Util.List as List

diagonalization : ℕ × ℕ → ℕ
diagonalization (x , y) = List.sum (List.upTo (suc (x + y))) + x

diagonalization⁻¹ : ℕ → ℕ × ℕ
diagonalization⁻¹ n = go (suc n) n zero
  module diagonalization⁻¹-implementation where
  go : ℕ → ℕ → ℕ → ℕ × ℕ
  go zero n i = zero , i
  go (suc fuel) n i with suc i ≤? n
  go (suc fuel) n i | yes i<n = go fuel (n ∸ suc i) (suc i)
  go (suc fuel) n i | no i≥n = n , i ∸ n


diagonalization-injective : diagonalization⁻¹ ∘ diagonalization ≗ id
diagonalization-injective (x , y) = lemma (suc n) zero (ℕ.n<1+n n) z≤n
  where
  n : ℕ
  n = diagonalization (x , y)

  open diagonalization⁻¹-implementation n

  lemma : ∀ (fuel i : ℕ) → n ∸ List.sum (List.upTo (suc i)) < fuel → i ≤ x + y → go fuel (n ∸ List.sum (List.upTo (suc i))) i ≡ (x , y)
  lemma zero i n<fuel i≤x+y = ⊥-elim (ℕ.n≮0 n<fuel)
  lemma (suc fuel) i n<fuel i≤x+y with suc i ≤? n ∸ List.sum (List.upTo (suc i))
  lemma (suc fuel) i n<fuel i≤x+y | yes i<n with x + y ≤? i
  lemma (suc fuel) i n<fuel i≤x+y | yes i<n | no x+y>i =
      go fuel (n ∸ List.sum (List.upTo (suc i)) ∸ suc i) (suc i)
    ≡⟨ Eq.cong (λ x → go fuel x (suc i)) (ℕ.∸-+-assoc n (List.sum (List.upTo (suc i))) (suc i)) ⟩
      go fuel (n ∸ (List.sum (List.upTo (suc i)) + suc i)) (suc i)
    ≡⟨ Eq.cong (λ x → go fuel (n ∸ (List.sum (List.upTo (suc i)) + x)) (suc i)) (ℕ.+-identityʳ (suc i)) ⟨
      go fuel (n ∸ (List.sum (List.upTo (suc i)) + (suc i + 0))) (suc i)
    ≡⟨ Eq.cong (λ x → go fuel (n ∸ x) (suc i)) (List.sum-++ (List.upTo (suc i)) (suc i ∷ [])) ⟨
      go fuel (n ∸ (List.sum (List.upTo (suc i) ∷ʳ suc i))) (suc i)
    ≡⟨ Eq.cong (λ x → go fuel (n ∸ List.sum x) (suc i)) (List.applyUpTo-∷ʳ⁺ id (suc i)) ⟩
      go fuel (n ∸ List.sum (List.upTo (suc (suc i)))) (suc i)
    ≡⟨ lemma fuel (suc i) n<fuel' (ℕ.≰⇒> x+y>i) ⟩
      x , y
    ∎
    where
    n<fuel' : n ∸ List.sum (List.upTo (suc (suc i))) < fuel
    n<fuel' =
      begin-strict
        n ∸ List.sum (List.upTo (suc (suc i)))
      ≡⟨ Eq.cong (λ x → n ∸ List.sum x) (List.applyUpTo-∷ʳ⁺ id (suc i)) ⟨
        n ∸ List.sum (List.upTo (suc i) ∷ʳ suc i)
      ≡⟨ Eq.cong (n ∸_) (List.sum-++ (List.upTo (suc i)) (suc i ∷ [])) ⟩
        n ∸ (List.sum (List.upTo (suc i)) + (suc i + 0))
      ≤⟨ ℕ.∸-monoʳ-≤ n (ℕ.+-monoʳ-≤ (List.sum (List.upTo (suc i))) (s≤s z≤n)) ⟩
        n ∸ (List.sum (List.upTo (suc i)) + 1)
      ≡⟨ ℕ.∸-+-assoc n (List.sum (List.upTo (suc i))) 1 ⟨
        n ∸ List.sum (List.upTo (suc i)) ∸ 1
      <⟨ ℕ.∸-monoˡ-< n<fuel (ℕ.≤-trans (s≤s z≤n) i<n) ⟩
        suc fuel ∸ 1
      ≡⟨⟩
        fuel
      ∎
      where
      open ℕ.≤-Reasoning

    open Eq.≡-Reasoning
  lemma (suc fuel) i n<fuel i≤x+y | yes i<n | yes x+y≤i = ⊥-elim (ℕ.n≮n x (
    begin-strict
      x
    ≤⟨ ℕ.m≤m+n x y ⟩
      x + y
    ≤⟨ x+y≤i ⟩
      i
    <⟨ i<n ⟩
      List.sum (List.upTo (suc (x + y))) + x ∸ List.sum (List.upTo (suc i))
    ≡⟨ Eq.cong (λ y → List.sum (List.upTo (suc y)) + x ∸ List.sum (List.upTo (suc i))) (ℕ.≤-antisym x+y≤i i≤x+y) ⟩
      List.sum (List.upTo (suc i)) + x ∸ List.sum (List.upTo (suc i))
    ≡⟨ ℕ.m+n∸m≡n (List.sum (List.upTo (suc i))) x ⟩
      x
    ∎))
    where
    open ℕ.≤-Reasoning
  lemma (suc fuel) i n<fuel i≤x+y | no i<n with x + y ≤? i
  lemma (suc fuel) i n<fuel i≤x+y | no i<n | yes x+y≤i = Eq.cong₂ _,_ x-correct y-correct
    where
    open Eq.≡-Reasoning

    i≡x+y : i ≡ x + y
    i≡x+y = ℕ.≤-antisym i≤x+y x+y≤i

    x-correct : n ∸ List.sum (List.upTo (suc i)) ≡ x
    x-correct =
        n ∸ List.sum (List.upTo (suc i))
      ≡⟨ Eq.cong (λ x → n ∸ List.sum (List.upTo (suc x))) i≡x+y ⟩
        n ∸ List.sum (List.upTo (suc (x + y)))
      ≡⟨⟩
        List.sum (List.upTo (suc (x + y))) + x ∸ List.sum (List.upTo (suc (x + y)))
      ≡⟨ ℕ.+-∸-comm x (ℕ.≤-refl {x = List.sum (List.upTo (suc (x + y)))}) ⟩
        List.sum (List.upTo (suc (x + y))) ∸ List.sum (List.upTo (suc (x + y))) + x
      ≡⟨ Eq.cong (_+ x) (ℕ.n∸n≡0 (List.sum (List.upTo (suc (x + y))))) ⟩
        x
      ∎

    y-correct : i ∸ (n ∸ List.sum (List.upTo (suc i))) ≡ y
    y-correct =
        i ∸ (n ∸ List.sum (List.upTo (suc i)))
      ≡⟨ Eq.cong (i ∸_) x-correct ⟩
        i ∸ x
      ≡⟨ Eq.cong (_∸ x) i≡x+y ⟩
        x + y ∸ x
      ≡⟨ ℕ.+-∸-comm y (ℕ.≤-refl {x = x}) ⟩
        x ∸ x + y
      ≡⟨ Eq.cong (_+ y) (ℕ.n∸n≡0 x) ⟩
        y
      ∎
  lemma (suc fuel) i n<fuel i≤x+y | no i<n | no x+y≰i = ⊥-elim (ℕ.n≮n (x + y) (
    begin-strict
      x + y
    ≤⟨ List.upTo-m∸upTo-n>m (ℕ.≰⇒> x+y≰i) ⟩
      List.sum (List.upTo (suc (x + y))) ∸ List.sum (List.upTo (suc i))
    ≤⟨ ℕ.∸-monoˡ-≤ (List.sum (List.upTo (suc i))) (ℕ.m≤m+n (List.sum (List.upTo (suc (x + y)))) x) ⟩
      List.sum (List.upTo (suc (x + y))) + x ∸ List.sum (List.upTo (suc i))
    ≡⟨⟩
      n ∸ List.sum (List.upTo (suc i))
    <⟨ ℕ.≰⇒> i<n ⟩
      suc i
    ≤⟨ ℕ.≰⇒> x+y≰i ⟩
      x + y
    ∎))
    where
    open ℕ.≤-Reasoning

diagonalization-surjective : diagonalization ∘ diagonalization⁻¹ ≗ id
diagonalization-surjective n = lemma (suc n) n zero (ℕ.n<1+n n) refl
  where
  open diagonalization⁻¹-implementation n

  lemma : (fuel n' i : ℕ) → n ∸ List.sum (List.upTo (suc i)) < fuel → List.sum (List.upTo (suc i)) + n' ≡ n → diagonalization (go fuel n' i) ≡ n
  lemma zero n' i n<fuel upTo+n'≡n = ⊥-elim (ℕ.n≮0 n<fuel)
  lemma (suc fuel) n' i n<fuel upTo+n'≡n with suc i ≤? n'
  lemma (suc fuel) n' i n<fuel upTo+n'≡n | yes i<n' = lemma fuel (n' ∸ suc i) (suc i) n<fuel' ((
      List.sum (List.upTo (suc (suc i))) + (n' ∸ suc i)
    ≡⟨ Eq.cong (λ x → List.sum x + (n' ∸ suc i)) (List.applyUpTo-∷ʳ⁺ id (suc i)) ⟨
      List.sum (List.upTo (suc i) ∷ʳ suc i) + (n' ∸ suc i)
    ≡⟨ Eq.cong (_+ (n' ∸ suc i)) (List.sum-++ (List.upTo (suc i)) (suc i ∷ [])) ⟩
      List.sum (List.upTo (suc i)) + (suc i + zero) + (n' ∸ suc i)
    ≡⟨ Eq.cong (λ x → List.sum (List.upTo (suc i)) + x + (n' ∸ suc i)) (ℕ.+-identityʳ (suc i)) ⟩
      List.sum (List.upTo (suc i)) + suc i + (n' ∸ suc i)
    ≡⟨ ℕ.+-assoc (List.sum (List.upTo (suc i))) (suc i) (n' ∸ suc i) ⟩
      List.sum (List.upTo (suc i)) + (suc i + (n' ∸ suc i))
    ≡⟨ Eq.cong (List.sum (List.upTo (suc i)) +_) (ℕ.+-∸-assoc (suc i) i<n') ⟨
      List.sum (List.upTo (suc i)) + (suc i + n' ∸ suc i)
    ≡⟨ Eq.cong (List.sum (List.upTo (suc i)) +_) (ℕ.m+n∸m≡n (suc i) n') ⟩
      List.sum (List.upTo (suc i)) + n'
    ≡⟨ upTo+n'≡n ⟩
      n
    ∎))
    where
    n<fuel' : n ∸ List.sum (List.upTo (suc (suc i))) < fuel
    n<fuel' =
      begin-strict
        n ∸ List.sum (List.upTo (suc (suc i)))
      ≡⟨ Eq.cong (λ x → n ∸ List.sum x) (List.applyUpTo-∷ʳ⁺ id (suc i)) ⟨
        n ∸ List.sum (List.upTo (suc i) ∷ʳ suc i)
      ≡⟨ Eq.cong (n ∸_) (List.sum-++ (List.upTo (suc i)) (suc i ∷ [])) ⟩
        n ∸ (List.sum (List.upTo (suc i)) + (suc i + 0))
      ≤⟨ ℕ.∸-monoʳ-≤ n (ℕ.+-monoʳ-≤ (List.sum (List.upTo (suc i))) (s≤s z≤n)) ⟩
        n ∸ (List.sum (List.upTo (suc i)) + 1)
      ≡⟨ ℕ.∸-+-assoc n (List.sum (List.upTo (suc i))) 1 ⟨
        n ∸ List.sum (List.upTo (suc i)) ∸ 1
      <⟨ ℕ.∸-monoˡ-< n<fuel (ℕ.≤-trans (s≤s z≤n) (
        begin
         1
        ≤⟨ s≤s z≤n ⟩
         suc i
        ≤⟨ i<n' ⟩
          n'
        ≡⟨ ℕ.m+n∸m≡n (List.sum (List.upTo (suc i))) n' ⟨
          List.sum (List.upTo (suc i)) + n' ∸ List.sum (List.upTo (suc i))
        ≡⟨ Eq.cong (_∸ List.sum (List.upTo (suc i))) upTo+n'≡n ⟩
          n ∸ List.sum (List.upTo (suc i))
        ∎))
      ⟩
        suc fuel ∸ 1
      ≡⟨⟩
        fuel
      ∎
      where
      open ℕ.≤-Reasoning

    open Eq.≡-Reasoning
  lemma (suc fuel) n' i n<fuel upTo+n'≡n | no i≥n' =
      diagonalization (n' , i ∸ n')
    ≡⟨⟩
      List.sum (List.upTo (suc (n' + (i ∸ n')))) + n'
    ≡⟨ Eq.cong (λ x → List.sum (List.upTo (suc x)) + n') (ℕ.+-∸-assoc n' (ℕ.≤-pred (ℕ.≰⇒> i≥n'))) ⟨
      List.sum (List.upTo (suc (n' + i ∸ n'))) + n'
    ≡⟨ Eq.cong (λ x → List.sum (List.upTo (suc x)) + n') (ℕ.m+n∸m≡n n' i) ⟩
      List.sum (List.upTo (suc i)) + n'
    ≡⟨ upTo+n'≡n ⟩
      n
    ∎
    where
    open Eq.≡-Reasoning
