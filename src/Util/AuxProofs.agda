module Util.AuxProofs where

open import Data.Nat.Base
open import Data.Fin.Base using (Fin; fromℕ<)

open import Data.Nat.Properties using (m⊓n≤m)

m≤n⇒m<1+n : ∀ (m n : ℕ)
  → m ≤ n
    ---------
  → m < suc n -- suc m ≤ suc n

m≤n⇒m<1+n zero n m≤n = s≤s z≤n
m≤n⇒m<1+n (suc m) (suc n) sm≤sn = s≤s sm≤sn

{-|
Takes the minium of the two given numbers and proves that the result is smaller than 1 + the first number.
To prove that the result is smaller than 1 + the second number, use flip to sap the arguments of this function.
-}
minFinFromLimit : (n-1 : ℕ) → ℕ → Fin (suc n-1)
minFinFromLimit n-1 t =
  let min = n-1 ⊓ t
      x = m⊓n≤m n-1 t
   in fromℕ< (m≤n⇒m<1+n min n-1 x)

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
