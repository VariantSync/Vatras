module Util.Function where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

cong-app₂ : ∀ {ℓ} {A C : Set ℓ} {T : A → Set ℓ} {x y : A} {tx : T x} {ty : T y}
  → (f : (a : A) → T a → C)
  → x ≡ y
  → (∀ (a : A) (t u : T a) → t ≡ u)
  → f x tx ≡ f y ty
cong-app₂ {y = y} {tx = tx} {ty = ty} f refl T-cong = Eq.cong (f y) (T-cong y tx ty)
