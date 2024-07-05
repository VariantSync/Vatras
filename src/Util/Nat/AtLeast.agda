module Util.Nat.AtLeast where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; s≤s)
open import Data.Nat.Properties as ℕ using (m+n≤o⇒n≤o; ≤-reflexive)
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.List as List
open import Data.List.NonEmpty using (List⁺; _∷_)

-- A natural number greater than `n`.
-- Hereby, `sucs` represents `n` consecutive `suc`s.
-- See `toℕ` for the semantics of `sucs`.
data ℕ≥ (n : ℕ) : Set where
  sucs : ℕ → ℕ≥ n

toℕ : {n : ℕ} → ℕ≥ n → ℕ
toℕ {n} (sucs k) = n + k

pred : {n : ℕ} → ℕ≥ (suc n) → ℕ≥ n
pred (sucs n) = sucs n

_≤_ : {n m : ℕ} → ℕ≥ n → ℕ≥ m → Set
n ≤ m = toℕ n ℕ.≤ toℕ m

_<_ : {n m : ℕ} → ℕ≥ n → ℕ≥ m → Set
n < m = toℕ n ℕ.< toℕ m

lift≤ : {k n m : ℕ} → n ℕ.≤ m → sucs {k} n ≤ sucs {k} m
lift≤ {k} n≤m = ℕ.+-monoʳ-≤ k n≤m

≤-toℕ : {n : ℕ} → (m : ℕ≥ n) → n ℕ.≤ toℕ m
≤-toℕ (sucs m) = ℕ.m≤n⇒m≤n+o m (ℕ.≤-reflexive refl)

-- Convert a natural number into a finite number by using the maximum number for too big numbers.
cappedFin : {n : ℕ≥ 1} → ℕ → Fin (toℕ n)
cappedFin {sucs zero} m = zero
cappedFin {sucs (suc n)} zero = zero
cappedFin {sucs (suc n)} (suc m) = suc (cappedFin m)

cappedFin-toℕ : ∀ {n : ℕ}
  → (m : Fin (suc n))
  → cappedFin {sucs n} (Fin.toℕ {suc n} m) ≡ m
cappedFin-toℕ {zero} zero = refl
cappedFin-toℕ {suc n} zero = refl
cappedFin-toℕ {suc n} (suc m) = Eq.cong suc (cappedFin-toℕ {n} m)

cappedFin-idempotent : ∀ {n₁ n₂ : ℕ}
  → (n₁ ℕ.≤ n₂)
  → (m : ℕ)
  → cappedFin {sucs n₁} (Fin.toℕ (cappedFin {sucs n₂} m)) ≡ cappedFin {sucs n₁} m
cappedFin-idempotent {zero} {n₂} n₁≤n₂ zero = refl
cappedFin-idempotent {zero} {n₂} n₁≤n₂ (suc m) = refl
cappedFin-idempotent {suc n₁} {suc n₂} n₁≤n₂ zero = refl
cappedFin-idempotent {suc n₁} {suc n₂} (s≤s n₁≤n₂) (suc m) = Eq.cong suc (cappedFin-idempotent {n₁} {n₂} n₁≤n₂ m)

cast-cappedFin : ∀ {n m : ℕ} (k : ℕ)
  → (eq : suc n ≡ suc m)
  → Fin.cast eq (cappedFin {sucs n} k) ≡ cappedFin {sucs m} k
cast-cappedFin {n = zero} k refl = refl
cast-cappedFin {n = suc n} zero refl = refl
cast-cappedFin {n = suc n} (suc k) refl = Eq.cong suc (cast-cappedFin {n = n} k refl)

_⊔_ : {n : ℕ} → ℕ≥ n → ℕ≥ n → ℕ≥ n
_⊔_ (sucs n) (sucs m) = sucs (n ℕ.⊔ m)

⊔-comm : {k : ℕ} → (n m : ℕ≥ k) → n ⊔ m ≡ m ⊔ n
⊔-comm (sucs n) (sucs m) = Eq.cong sucs (ℕ.⊔-comm n m)

toℕ-⊔ : ∀ {k : ℕ} → (n m : ℕ≥ k) → toℕ (n ⊔ m) ≡ toℕ n ℕ.⊔ toℕ m
toℕ-⊔ {k} (sucs n) (sucs m) = ℕ.mono-≤-distrib-⊔ (ℕ.+-monoʳ-≤ k) n m

m≤m⊔n : ∀ {k : ℕ} → (m n : ℕ≥ k) → m ≤ (m ⊔ n)
m≤m⊔n (sucs m) (sucs n) = lift≤ (ℕ.m≤m⊔n m n)

m≤n⊔m : ∀ {k : ℕ} → (n m : ℕ≥ k) → m ≤ (n ⊔ m)
m≤n⊔m (sucs m) (sucs n) = lift≤ (ℕ.m≤n⊔m m n)
