module Util.Vec where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.List.Properties as List
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
import Util.List as List
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

saturate : ∀ {A : Set} {n : ℕ≥ 1} {m : ℕ}
  → ℕ≥.toℕ n ≤ m
  → Vec A (ℕ≥.toℕ n)
  → Vec A m
saturate {n = sucs zero} {m = suc zero} suc-n≤m (x ∷ []) = x ∷ []
saturate {n = sucs zero} {m = suc (suc m)} suc-n≤m (x ∷ []) = x ∷ saturate (s≤s z≤n) (x ∷ [])
saturate {n = sucs (suc n)} {m = m} (s≤s suc-n≤m) (x ∷ xs) = x ∷ saturate suc-n≤m xs

saturate-map : ∀ {n : ℕ≥ 1} {m : ℕ} {A B : Set}
  → (n≤m : ℕ≥.toℕ n ≤ m)
  → (f : A → B)
  → (vec : Vec A (ℕ≥.toℕ n))
  → saturate {n = n} n≤m (Vec.map f vec) ≡ Vec.map f (saturate {n = n} n≤m vec)
saturate-map {sucs zero} {suc zero} (s≤s n≤m) f (x ∷ []) = refl
saturate-map {sucs zero} {suc (suc m)} (s≤s n≤m) f (x ∷ [])
  rewrite saturate-map {sucs zero} {suc m} (s≤s z≤n) f (x ∷ [])
  = refl
saturate-map {sucs (suc n)} {m} (s≤s n≤m) f (x ∷ xs)
  rewrite saturate-map n≤m f xs
  = refl

lookup-saturate : ∀ {A : Set} {n : ℕ≥ 1} {m : ℕ}
  → (n≤m : ℕ≥.toℕ n ≤ m)
  → (vec : Vec A (ℕ≥.toℕ n))
  → (i : Fin m)
  → Vec.lookup (saturate {n = n} n≤m vec) i ≡ Vec.lookup vec (ℕ≥.cappedFin {n} (Fin.toℕ i))
lookup-saturate {n = sucs zero} {m = suc zero} n≤m (x ∷ []) zero = refl
lookup-saturate {n = sucs zero} {m = suc (suc m)} n≤m (x ∷ []) zero = refl
lookup-saturate {n = sucs zero} {m = suc (suc m)} n≤m (x ∷ []) (suc i) = lookup-saturate (s≤s z≤n) (x ∷ []) i
lookup-saturate {n = sucs (suc n)} {m = suc m} (s≤s n≤m) (x ∷ xs) zero = refl
lookup-saturate {n = sucs (suc n)} {m = suc m} (s≤s n≤m) (x ∷ xs) (suc i) = lookup-saturate n≤m xs i
