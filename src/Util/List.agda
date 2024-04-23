{-|
Utilities for lists.
-}
module Util.List where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n)
open import Data.List as List using (List; []; _∷_; lookup; foldr)
open import Data.List.Properties using (map-id; length-++)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; toList; _⁺++⁺_) renaming (map to map⁺)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Function using (id; _∘_; flip)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

-- true iff the given list is empty
empty? : ∀ {A : Set} → List A → Bool
empty? [] = true
empty? (_ ∷ _) = false

max : List ℕ → ℕ
max = foldr _⊔_ zero

-- TODO: Contribute to stl
⁺++⁺-length : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A)
  → List⁺.length (xs ⁺++⁺ ys) ≡ List⁺.length xs + List⁺.length ys
⁺++⁺-length (x ∷ xs) (y ∷ ys) = length-++ (x ∷ xs)

⁺++⁺-length-≤ : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A) → List⁺.length xs ≤ List⁺.length (xs ⁺++⁺ ys)
⁺++⁺-length-≤ xs ys rewrite ⁺++⁺-length xs ys = m≤m+n (List⁺.length xs) (List⁺.length ys)

-- Do not touch this function. its definition is very fragile and just refactoring it can break proofs.
find-or-last : ∀ {ℓ} {A : Set ℓ} → ℕ → List⁺ A → A
find-or-last _ (x ∷ []) = x
find-or-last zero (x ∷ y ∷ zs) = x
find-or-last (suc i) (x ∷ y ∷ zs) = find-or-last i (y ∷ zs)
-- find-or-last (x ∷ []) _ = x
-- find-or-last (x ∷ y ∷ zs) zero = x
-- find-or-last (x ∷ y ∷ zs) (suc i) = find-or-last (y ∷ zs) i

find-or-last-zero : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : List A)
  → find-or-last zero (x ∷ xs) ≡ x
find-or-last-zero _ [] = refl
find-or-last-zero _ (_ ∷ _) = refl

map-find-or-last : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → (i : ℕ)
  → f ∘ (find-or-last i) ≗ (find-or-last i) ∘ (map⁺ f)
map-find-or-last f zero (head ∷ []) = refl
map-find-or-last f zero (head ∷ x ∷ tail) = refl
map-find-or-last f (suc i) (x ∷ []) = refl
map-find-or-last f (suc i) (x ∷ y ∷ zs) =
  begin
    (f ∘ find-or-last (suc i)) (x ∷ y ∷ zs)
  ≡⟨⟩
    (f ∘ find-or-last i) (y ∷ zs)
  ≡⟨ map-find-or-last f i (y ∷ zs) ⟩
    (find-or-last i ∘ map⁺ f) (y ∷ zs)
  ≡⟨⟩
    (find-or-last (suc i) ∘ map⁺ f) (x ∷ y ∷ zs)
  ∎

find-or-last⇒lookup : ∀ {ℓ} {A : Set ℓ} {i : ℕ}
  → (x : A)
  → (xs : List A)
  → find-or-last i (x ∷ xs) ≡ Vec.lookup (x ∷ Vec.fromList xs) (ℕ≥.cappedFin i)
find-or-last⇒lookup {i = i} x [] = refl
find-or-last⇒lookup {i = zero} x (y ∷ ys) = refl
find-or-last⇒lookup {i = suc i} x (y ∷ ys) = find-or-last⇒lookup y ys

lookup⇒find-or-last : ∀ {ℓ} {A : Set ℓ} {n m : ℕ}
  → (vec : Vec A (suc n))
  → Vec.lookup vec (ℕ≥.cappedFin m) ≡ find-or-last m (List⁺.fromVec vec)
lookup⇒find-or-last {n = zero} {m = m} (x ∷ []) = refl
lookup⇒find-or-last {n = suc n} {m = zero} (x ∷ y ∷ ys) = refl
lookup⇒find-or-last {n = suc n} {m = suc m} (x ∷ y ∷ ys) = lookup⇒find-or-last (y ∷ ys)

find-or-last-append : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → n < List⁺.length xs
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last n xs
find-or-last-append {n = .zero} (x ∷ [])     (y ∷ ys) (s≤s z≤n) = refl
find-or-last-append {n =  zero} (x ∷ z ∷ zs) (y ∷ ys) (s≤s le)  = refl
find-or-last-append {n = suc n} (x ∷ z ∷ zs) (y ∷ ys) (s≤s (n≤zzs)) = find-or-last-append (z ∷ zs) (y ∷ ys) (n≤zzs)

find-or-last-prepend-+ : ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ)
  → (xs ys : List⁺ A)
  → find-or-last (List⁺.length xs + n) (xs ⁺++⁺ ys) ≡ find-or-last n ys
find-or-last-prepend-+ n (x ∷ xs) ys = ind n x xs ys
  where
    -- We need this indirection for termination checking.
    -- We have to unpack the first list into two parameters.
    ind : ∀ {ℓ} {A : Set ℓ}
      → (n : ℕ)
      → (x : A)
      → (xs : List A)
      → (ys : List⁺ A)
      → find-or-last (List⁺.length (x ∷ xs) + n) ((x ∷ xs) ⁺++⁺ ys) ≡ find-or-last n ys
    ind n x [] ys = refl
    ind n x (z ∷ zs) ys = ind n z zs ys

find-or-last-prepend-∸ : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → List⁺.length xs ≤ n
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last (n ∸ List⁺.length xs) ys
find-or-last-prepend-∸ {n = zero} xs ys ()
find-or-last-prepend-∸ {n = suc n} (x ∷ []) ys (s≤s z≤n) = refl
find-or-last-prepend-∸ {n = suc n} (x ∷ z ∷ zs) ys (s≤s smol) =
  begin
    find-or-last (suc n) ((x ∷ z ∷ zs) ⁺++⁺ ys)
  ≡⟨⟩
    find-or-last n ((z ∷ zs) ⁺++⁺ ys)
  ≡⟨ find-or-last-prepend-∸ (z ∷ zs) ys smol ⟩
    find-or-last (n ∸ List⁺.length (z ∷ zs)) ys
  ≡⟨⟩
    find-or-last (suc n ∸ suc (List⁺.length (z ∷ zs))) ys
  ≡⟨⟩
    find-or-last (suc n ∸ List⁺.length (x ∷ z ∷ zs)) ys
  ∎

-- Todo: Contribute this to Agda stdlib
map⁺-id : ∀ {ℓ} {A : Set ℓ} → map⁺ id ≗ id {A = List⁺ A}
map⁺-id (head ∷ tail) = Eq.cong (head ∷_) (map-id tail)
