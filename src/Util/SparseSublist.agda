module Util.SparseSublist where

open import Framework.Definitions using (𝔸; atoms)
open import Data.Product using (proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)

{-|
Given two lists A and B.
All elements in A also appear in B in the same order they appear in A.
The elements do not have to be continous, i.e., there might be interspersed other elements in B.
The elements are left-aligned, i.e., each element in A is matched to the leftmost matching element in B.
-}
data _is-sparse-sublist-of_ {ℓ} {A : Set ℓ} : List A → List A → Set ℓ where
  sub-base : ∀ {p : List A}
      ------------------------
    → [] is-sparse-sublist-of p

  step-match : ∀ {p q : List A} {a : A}
    → p is-sparse-sublist-of q
      ------------------------------------
    → (a ∷ p) is-sparse-sublist-of (a ∷ q)

  step-diff : ∀ {p q : List A} {a b : A}
    → ¬ (a ≡ b)
    → (a ∷ p) is-sparse-sublist-of q
      ------------------------------------
    → (a ∷ p) is-sparse-sublist-of (b ∷ q)

_in-list_ : ∀ {ℓ} {A : Set ℓ} → A → List A → Set ℓ
x in-list ys = (x ∷ []) is-sparse-sublist-of ys

module _ {AtomSet : 𝔸} where
  private
    A = atoms AtomSet
    _≟_ = proj₂ AtomSet

  mutual
    drop-head : ∀ {x : A} {xs ys : List A}
      → (x ∷ xs) is-sparse-sublist-of ys
      →      xs  is-sparse-sublist-of ys
    drop-head {x} {xs} {.(x ∷ _)} (step-match sub) = step-any x sub
    drop-head {x} {[]} {y ∷ ys} (step-diff x≢y sub) = sub-base
    drop-head {x} {z ∷ zs} {y ∷ ys} (step-diff x≢y sub) with z ≟ y
    ... | yes refl = step-match (drop-head (drop-head sub))
    ... | no  z≢y  = step-diff z≢y (drop-head sub)

    step-any : ∀ {xs ys : List A} (z : A)
      → xs is-sparse-sublist-of ys
      → xs is-sparse-sublist-of (z ∷ ys)
    step-any {[]} _ sub-base = sub-base
    step-any {x ∷ xs} z sub with x ≟ z
    ... | no  x≢z  = step-diff x≢z sub
    step-any {x ∷ xs} {y ∷ ys} x sub | yes refl = step-match (drop-head sub)

_ : (1 ∷ 2 ∷ 3 ∷ []) is-sparse-sublist-of (1 ∷ 2 ∷ 3 ∷ [])
_ = step-match (step-match (step-match sub-base))

_ : (2 ∷ []) is-sparse-sublist-of (1 ∷ 2 ∷ 3 ∷ [])
_ = step-diff (λ ()) (step-match sub-base)

test1 : (2 ∷ 2 ∷ []) is-sparse-sublist-of (1 ∷ 2 ∷ 3 ∷ 2 ∷ 2 ∷ 2 ∷ [])
test1 = step-diff (λ ()) (step-match (step-diff (λ ()) (step-match sub-base)))

_ : (2 ∷ 2 ∷ []) is-sparse-sublist-of (0 ∷ 1 ∷ 2 ∷ 3 ∷ 2 ∷ 2 ∷ 2 ∷ [])
_ = step-diff (λ ()) test1

_ : (2 ∷ 2 ∷ []) is-sparse-sublist-of (2 ∷ 1 ∷ 2 ∷ 3 ∷ 2 ∷ 2 ∷ 2 ∷ [])
_ = step-match (step-diff (λ ()) (step-match sub-base))

step-diff' : ∀ {ℓ} {A : Set ℓ} {xs : List A} {y : A} {ys : List A}
  → All (_≢ y) xs -- this is actually too strong
  → xs is-sparse-sublist-of ys
  → xs is-sparse-sublist-of (y ∷ ys)
step-diff' {xs = []} _ _ = sub-base
step-diff' {xs = x ∷ xs} (x≢y ∷ _) sub = step-diff x≢y sub

sparse-sublist-refl : ∀ {ℓ} {A : Set ℓ} (xs : List A) → xs is-sparse-sublist-of xs
sparse-sublist-refl [] = sub-base
sparse-sublist-refl (x ∷ xs) = step-match (sparse-sublist-refl xs)

sparse-sublist-head : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A)
  → (x ∷ xs) is-sparse-sublist-of ys
  → (x ∷ []) is-sparse-sublist-of ys
sparse-sublist-head x xs (.x ∷ ys) (step-match sub) = step-match sub-base
sparse-sublist-head x xs (y ∷ ys) (step-diff x≢y sub) = step-diff x≢y (sparse-sublist-head x xs ys sub)

-- sparse-sublist-append-to-tail : ∀ {ℓ} {A : Set ℓ} (xs : List A) (y : A) (ys : List A)
--   → xs is-sparse-sublist-of ys
--   → xs is-sparse-sublist-of (y ∷ ys)
-- sparse-sublist-append-to-tail [] y ys sub = sub-base
-- sparse-sublist-append-to-tail (x ∷ xs) y ys sub = {!!}

-- data _in-list_ {ℓ} {A : Set ℓ} : A → List A → Set ℓ where
--   in-here : ∀ {x xs} → x in-list (x ∷ xs)
  --   in-there : ∀ {x y ys}
  --     → ¬ (x ≡ y)
  --     → x in-list ys
  --     → x in-list (y ∷ ys)
