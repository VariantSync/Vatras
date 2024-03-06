{-# OPTIONS --allow-unsolved-metas #-}

{-|
Utilities for lists.
-}
module Util.List where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.List as List using (List; []; _∷_; lookup; foldr)
open import Data.List.Properties using (map-id; length-++)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; toList; _⁺++⁺_) renaming (map to map⁺)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Util.AuxProofs using (minFinFromLimit; clamp)
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
length-⁺++⁺ : ∀ {ℓ} {A : Set ℓ} (xs ys : List⁺ A)
  → List⁺.length (xs ⁺++⁺ ys) ≡ List⁺.length xs + List⁺.length ys
length-⁺++⁺ (x ∷ xs) (y ∷ ys) = length-++ (x ∷ xs)

-- Selects the alternative at the given tag.
lookup-clamped : {A : Set} → ℕ → List⁺ A → A
lookup-clamped n list⁺ =
  let list = toList list⁺
   in lookup list (clamp (List.length list) n)

-- alternative to lookup-clamped that is easier to handle in proofs
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

find-or-last⇒lookup : ∀ {A : Set} {i : ℕ}
  → (x : A)
  → (xs : List A)
  → find-or-last i (x ∷ xs) ≡ Vec.lookup (x ∷ Vec.fromList xs) (ℕ≥.cappedFin i)
find-or-last⇒lookup {i = i} x [] = refl
find-or-last⇒lookup {i = zero} x (y ∷ ys) = refl
find-or-last⇒lookup {i = suc i} x (y ∷ ys) = find-or-last⇒lookup y ys

lookup⇒find-or-last : ∀ {A : Set} {n m : ℕ}
  → (vec : Vec A (suc n))
  → Vec.lookup vec (ℕ≥.cappedFin m) ≡ find-or-last m (List⁺.fromVec vec)
lookup⇒find-or-last {n = zero} {m = m} (x ∷ []) = refl
lookup⇒find-or-last {n = suc n} {m = zero} (x ∷ y ∷ ys) = refl
lookup⇒find-or-last {n = suc n} {m = suc m} (x ∷ y ∷ ys) = lookup⇒find-or-last (y ∷ ys)

append-preserves : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → n < List⁺.length xs
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last n xs
append-preserves {n = .zero} (x ∷ [])     (y ∷ ys) (s≤s z≤n) = refl
append-preserves {n =  zero} (x ∷ z ∷ zs) (y ∷ ys) (s≤s le)  = refl
append-preserves {n = suc n} (x ∷ z ∷ zs) (y ∷ ys) (s≤s (n≤zzs)) = append-preserves (z ∷ zs) (y ∷ ys) (n≤zzs)

-- FIXME: Remove this macro
{-# TERMINATING #-}
prepend-preserves : ∀ {ℓ} {A : Set ℓ}
  → (n : ℕ)
  → (xs ys : List⁺ A)
  → find-or-last (List⁺.length xs + n) (xs ⁺++⁺ ys) ≡ find-or-last n ys
prepend-preserves n (x ∷ []) ys = refl
prepend-preserves n (x ∷ z ∷ zs) ys = prepend-preserves n (z ∷ zs) ys
-- prepend-preserves n (x ∷ z ∷ zs) (y ∷ ys) =
--   begin
--     find-or-last (length (x ∷ z ∷ zs) + n) ((x ∷ z ∷ zs) ⁺++⁺ (y ∷ ys))
--   ≡⟨⟩
--     find-or-last (length (x ∷ z ∷ zs) + n) (x ∷ ((z ∷ zs) ++ (y ∷ ys)))
--   ≡⟨⟩
--     find-or-last (length (z ∷ zs) + n) (((z ∷ zs) ⁺++⁺ (y ∷ ys)))
--   ≡⟨ prepend-preserves n (z ∷ zs) (y ∷ ys) ⟩
--     find-or-last n (y ∷ ys)
--   ∎

prepend-preserves' : ∀ {ℓ} {A : Set ℓ} {n : ℕ}
  → (xs ys : List⁺ A)
  → List⁺.length xs ≤ n
  → find-or-last n (xs ⁺++⁺ ys) ≡ find-or-last (n ∸ List⁺.length xs) ys
prepend-preserves' {n = zero} xs ys ()
prepend-preserves' {n = suc n} (x ∷ []) ys (s≤s z≤n) = refl
prepend-preserves' {n = suc n} (x ∷ z ∷ zs) ys (s≤s smol) =
  begin
    find-or-last (suc n) ((x ∷ z ∷ zs) ⁺++⁺ ys)
  ≡⟨ {!!} ⟩
    find-or-last (suc n ∸ List⁺.length (x ∷ z ∷ zs)) ys
  ∎

-- Todo: Contribute this to Agda stdlib
map⁺-id : ∀ {ℓ} {A : Set ℓ} → map⁺ id ≗ id {A = List⁺ A}
map⁺-id (head ∷ tail) = Eq.cong (head ∷_) (map-id tail)
