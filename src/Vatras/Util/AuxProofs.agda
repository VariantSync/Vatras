module Vatras.Util.AuxProofs where

open import Level using (Level)
open import Function using (id; _∘_)

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; n∸n≡0; m≤n+m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; _≗_; refl)
open Eq.≡-Reasoning

----- Some logic helpers

true≢false : ∀ {a : Bool}
  → a ≡ true
    ---------
  → a ≢ false
true≢false refl ()

----- Some arithmetic properties

≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≡ᵇ-< : ∀ {m n} → n < m → (m ≡ᵇ n) ≡ false
≡ᵇ-< {.(suc _)} {zero}  (s≤s _) = refl
≡ᵇ-< {suc m}    {suc n} (s≤s x) = ≡ᵇ-< x

m+n≢ᵇn : ∀ i n → (suc i + n ≡ᵇ n) ≡ false
m+n≢ᵇn i n = ≡ᵇ-< (s≤s (m≤n+m n i))

n<m→m≡ᵇn : ∀ {n m : ℕ} → n < m → (m ≡ᵇ n) ≡ false
n<m→m≡ᵇn {zero} (s≤s n<m) = refl
n<m→m≡ᵇn {suc n} (s≤s n<m) = n<m→m≡ᵇn n<m

n∸1+m<n∸m : {n m : ℕ} → suc m ≤ n → n ∸ suc m < n ∸ m
n∸1+m<n∸m {suc n} {zero} (s≤s m<n) = n<1+n n
n∸1+m<n∸m {suc n} {suc m} (s≤s m<n) = n∸1+m<n∸m m<n

----- Properties of Vectors

module Vec where
  open import Data.List using ([]; _∷_)
  open import Data.Vec using (Vec; []; cast; fromList; toList)

  vec0 : ∀ {A : Set} → Vec A zero
  vec0 = []

  {-|
  Zero vector but cast to have size n∸n.
  -}
  vec-n∸n : ∀ {A : Set} → (n : ℕ) → Vec A (n ∸ n)
  vec-n∸n l = cast (Eq.sym (n∸n≡0 l)) vec0

  id≗toList∘fromList : ∀ {ℓ : Level} {A : Set ℓ} → id ≗ (Data.Vec.toList {A = A}) ∘ Data.Vec.fromList
  id≗toList∘fromList [] = refl
  id≗toList∘fromList (x ∷ xs) =
    begin
      x ∷ xs
    ≡⟨ Eq.cong (x ∷_) (id≗toList∘fromList xs) ⟩
      x ∷ toList (fromList xs)
    ≡⟨⟩
      toList (fromList (x ∷ xs))
    ∎
open Vec public

decidableEquality-× : {A B : Set} → DecidableEquality A → DecidableEquality B → DecidableEquality (A × B)
decidableEquality-× _==A_ _==B_ (a₁ , b₁) (a₂ , b₂) with a₁ ==A a₂ with b₁ ==B b₂
... | yes refl | yes refl = yes refl
... | yes refl | no b₁≢b₂ = no λ eq → b₁≢b₂ (Eq.cong (λ where (a , b) → b) eq)
... | no a₁≢a₂ | _ = no λ eq → a₁≢a₂ (Eq.cong (λ where (a , b) → a) eq)
