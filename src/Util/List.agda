module Util.List where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero; NonZero)
open import Data.List using (List; []; _∷_; lookup; length)
open import Data.List.Properties using (map-id)
open import Data.List.NonEmpty using (List⁺; _∷_; toList) renaming (map to map⁺)
open import Util.AuxProofs using (minFinFromLimit; clamp)
open import Function using (id; _∘_; flip)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

-- Selects the alternative at the given tag.
lookup-clamped : {A : Set} → ℕ → List⁺ A → A
lookup-clamped n list⁺ =
  let list = toList list⁺
   in lookup list (clamp (length list) n)

-- alternative to lookup-clamped that is easier to handle in proofs
-- Do not touch this function. its definition is very fragile and just refactoring it can break proofs.
find-or-last : ∀ {ℓ} {A : Set ℓ} → ℕ → List⁺ A → A
find-or-last _ (x ∷ []) = x
find-or-last zero (x ∷ y ∷ zs) = x
find-or-last (suc i) (x ∷ y ∷ zs) = find-or-last i (y ∷ zs)
-- find-or-last (x ∷ []) _ = x
-- find-or-last (x ∷ y ∷ zs) zero = x
-- find-or-last (x ∷ y ∷ zs) (suc i) = find-or-last (y ∷ zs) i

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

-- Todo: Contribute this to Agda stdlib
map⁺-id : ∀ {ℓ} {A : Set ℓ} → map⁺ id ≗ id {A = List⁺ A}
map⁺-id (head ∷ tail) = Eq.cong (head ∷_) (map-id tail)
