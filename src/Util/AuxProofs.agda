module Util.AuxProofs where

open import Level using (Level)
open import Function using (id; _∘_)

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Nat using (ℕ; zero; suc; NonZero; _≡ᵇ_; _⊓_; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; m⊓n≤m; +-comm; +-∸-comm; n∸n≡0)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; _≗_; refl)
open Eq.≡-Reasoning

-- Some logic helpers

true≢false : ∀ {a : Bool}
  → a ≡ true
    ---------
  → a ≢ false
true≢false refl ()

----- Some aritmetic properties

n≡ᵇn : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
n≡ᵇn zero = refl
n≡ᵇn (suc n) = n≡ᵇn n

<-cong-+ˡ : ∀ {m n} (a : ℕ) → m < n → a + m < a + n
<-cong-+ˡ zero x = x
<-cong-+ˡ (suc a) x = s≤s (<-cong-+ˡ a x)

n<m→m≡ᵇn : ∀ {n m : ℕ} → n < m → (m ≡ᵇ n) ≡ false
n<m→m≡ᵇn {zero} (s≤s n<m) = refl
n<m→m≡ᵇn {suc n} (s≤s n<m) = n<m→m≡ᵇn n<m

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

n∸1+m<n∸m : {n m : ℕ} → suc m ≤ n → n ∸ suc m < n ∸ m
n∸1+m<n∸m {suc n} {zero} (s≤s m<n) = n<1+n n
n∸1+m<n∸m {suc n} {suc m} (s≤s m<n) = n∸1+m<n∸m m<n

----- Implementations of the min function.

{-|
Takes the minium of the two given numbers and proves that the result is smaller than 1 + the first number.
To prove that the result is smaller than 1 + the second number, use flip to sap the arguments of this function.
-}
minFinFromLimit : (n-1 : ℕ) → ℕ → Fin (suc n-1)
minFinFromLimit n-1 t = fromℕ< {n-1 ⊓ t} (s≤s (m⊓n≤m n-1 t))

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


----- Properties of if_then_else

if-idemp : ∀ {ℓ} {A : Set ℓ} {a : A}
  → (c : Bool)
    ------------------------
  → (if c then a else a) ≡ a
if-idemp false = refl
if-idemp true  = refl

if-idemp' : ∀ {ℓ} {A : Set ℓ}
  → (a : A)
    ------------------------
  → ∀ {c} → (if c then a else a) ≡ a
if-idemp' _ {b} = if-idemp b

if-swap : ∀ {A : Set} (x y : Bool) (a b : A)
  → (if x then a else (if y then a else b))
  ≡ (if y then a else (if x then a else b))
if-swap false _ _ _ = refl
if-swap true false _ _ = refl
if-swap true true _ _ = refl

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
