module Util.AuxProofs where

open import Level using (Level)
open import Function using (id; _∘_)

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; NonZero; _⊓_; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Fin using (Fin; zero; suc; fromℕ<)

open import Data.Nat.Properties using (m⊓n≤m; +-comm; +-∸-comm; n∸n≡0)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

m≤n⇒m<1+n : ∀ (m n : ℕ)
  → m ≤ n
    ---------
  → m < suc n -- suc m ≤ suc n

m≤n⇒m<1+n zero n m≤n = s≤s z≤n
m≤n⇒m<1+n (suc m) (suc n) sm≤sn = s≤s sm≤sn

1+[m-n]=[1+m]-n : ∀ (m n : ℕ) → (n ≤ m) → suc (m ∸ n) ≡ suc m ∸ n
1+[m-n]=[1+m]-n m n n≤m =
  begin
    suc (m ∸ n)
  ≡⟨⟩
    1 + (m ∸ n)
  ≡⟨ +-comm 1 (m ∸ n) ⟩
    (m ∸ n) + 1
  ≡⟨ Eq.sym (+-∸-comm 1 n≤m ) ⟩
    (m + 1) ∸ n
  ≡⟨ Eq.cong (_∸ n) (+-comm m 1) ⟩
    (1 + m) ∸ n
  ≡⟨⟩
    suc m ∸ n
  ∎

1+[m-[1+n]]=m-n : ∀ (m n : ℕ) → (n < m) → suc (m ∸ suc n) ≡ m ∸ n
1+[m-[1+n]]=m-n (suc m-1) n (s≤s n<m-1) =
  begin
    suc (suc m-1 ∸ suc n)
  ≡⟨ Eq.cong suc refl ⟩
    suc (m-1 ∸ n)
  ≡⟨ 1+[m-n]=[1+m]-n m-1 n n<m-1 ⟩
    suc m-1 ∸ n
  ∎

{-|
Takes the minium of the two given numbers and proves that the result is smaller than 1 + the first number.
To prove that the result is smaller than 1 + the second number, use flip to sap the arguments of this function.
-}
minFinFromLimit : (n-1 : ℕ) → ℕ → Fin (suc n-1)
minFinFromLimit n-1 t =
  let min = n-1 ⊓ t
      x = m⊓n≤m n-1 t
   in fromℕ< (m≤n⇒m<1+n min n-1 x)

{-|
Clamps a non-negative natural number at the given limit.
In case the given number is smaller than the given length, the number is returned, otherwise the length - 1.
-}
clamp : (n : ℕ) → {NonZero n} → ℕ → Fin n
clamp (suc n) = minFinFromLimit n


clampAt : (n : ℕ) → ℕ → Fin (suc n)
clampAt _ zero = zero
clampAt zero (suc _) = zero
clampAt (suc n) (suc c) = suc (clampAt n c)

if-idemp : ∀ {A : Set} {a : A}
  → (c : Bool)
    ------------------------
  → (if c then a else a) ≡ a
if-idemp false = refl
if-idemp true  = refl

if-cong : ∀ {A B : Set} {a b : A}
  → (c : Bool)
  → (P : A → B)
    -------------------------------------------------
  → (if c then P a else P b) ≡ P (if c then a else b)
if-cong false _ = refl
if-cong true  _ = refl

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
