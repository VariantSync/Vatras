module Vatras.Util.Suffix where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

-- TODO: Replace with "Suffix" from stl?
{-
This relation relates a list with all of it suffixes.
This relation is a partial order because it is
  - reflexive (by definition),
  - antisymmetric (yet to prove),
  - and transitive (to prove).
-}
data _endswith_ {ℓ} {A : Set ℓ} : List A → List A → Set ℓ where
  match : ∀ (p : List A)
      ------------
    → p endswith p -- reflexive

  later : ∀ {p q : List A} {a : A}
    → p endswith q
      ------------------
    → (a ∷ p) endswith q

endswith-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A}
  → xs endswith xs
endswith-refl {xs = xs} = match xs

endswith-shrink-suffix : ∀ {ℓ} {A : Set ℓ} {y : A} {xs ys : List A}
  → xs endswith (y ∷ ys)
  → xs endswith ys
endswith-shrink-suffix (match (y ∷ ys)) = later (match ys)
endswith-shrink-suffix (later x) = later (endswith-shrink-suffix x)

endswith-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A}
  → xs endswith ys
  → ys endswith zs
  → xs endswith zs
endswith-trans (match _) b = b
endswith-trans (later a) (match _) = later a
endswith-trans (later a) (later b) = later (endswith-trans (endswith-shrink-suffix a) b)

endswith-tail : ∀ {ℓ} {A : Set ℓ} {x y : A} {xs ys : List A}
  → ¬ x ≡ y
  → (x ∷ xs) endswith (y ∷ ys)
  → xs endswith (y ∷ ys)
endswith-tail neq (match .(_ ∷ _)) = ⊥-elim (neq refl)
endswith-tail neq (later x) = x

endswith-All : ∀ {ℓ p} {A : Set ℓ} {P : A → Set p} {xs ys : List A}
  → xs endswith ys
  → All P xs
  → All P ys
endswith-All (match _) all = all
endswith-All (later ends) (px ∷ pxs) = endswith-All ends pxs

endswith-Any : ∀ {ℓ p} {A : Set ℓ} {P : A → Set p} {xs ys : List A}
  → xs endswith ys
  → Any P ys
  → Any P xs
endswith-Any (match _) any = any
endswith-Any (later ends) any = there (endswith-Any ends any)
