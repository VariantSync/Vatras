module Data.ConveyorBelt where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; <⇒≤; n∸n≡0)
open import Data.List using (List; length)
open import Data.Vec using (Vec; _∷_; []; _∷ʳ_; cast; fromList)

open import Util.AuxProofs using (1+[m-[1+n]]=m-n; vec-n∸n)

open import Relation.Nullary.Decidable using (Dec; yes; no; True)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

private
  variable
    ℓ : Level

record ConveyorBelt (A B : Set ℓ) (workload workleft : ℕ) (a : workleft ≤ workload) : Set ℓ where
  constructor _↢_ -- \l->
  field
     processed   : Vec B (workload ∸ workleft)
     unprocessed : Vec A (workleft)
infix 4 _↢_

{-|
Puts the given list on a conveyor belt to process.
-}
putOnBelt : ∀ {A B : Set} → (work : List A) → ConveyorBelt A B (length work) (length work) ≤-refl
putOnBelt ls = vec-n∸n (length ls) ↢ fromList ls

{-|
Advance the conveyor belt by one using the given conversion function f.
-}
step :
  ∀ {A B : Set}
    {load left-1 : ℕ}
    {left≤load : left-1 < load}
  → (f : A → B)
  → ConveyorBelt A B load (suc left-1) left≤load
    --------------------------------------------
  → ConveyorBelt A B load left-1 (<⇒≤ left≤load)
step {_} {_} {load} {left-1} {left-1<load} f (ls ↢ (r ∷ rs)) =
  let next = cast (1+[m-[1+n]]=m-n load left-1 left-1<load) (ls ∷ʳ (f r))
   in next ↢ rs

{-|
Fully evaluate the conveyor belt.
Translates all remaining elements using the given conversion function.
-}
stepAll :
  ∀ {A B : Set}
    {load left : ℕ}
    {left≤load : left ≤ load}
  → (f : A → B)
  → ConveyorBelt A B load left left≤load
    ------------------------------------
  → ConveyorBelt A B load zero z≤n
stepAll f   (ls ↢ [])     = ls ↢ []
stepAll f c@(ls ↢ r ∷ rs) = stepAll f (step f c)

-- True iff nothing is left to process, false otherwise.
done :
  ∀ {A B : Set}
    {load left : ℕ}
    {left≤load : left ≤ load}
  → (belt : ConveyorBelt A B load left left≤load)
    ---------------------------------------------
  → Dec (left ≡ zero)
done (ls ↢ [])     = yes refl
done (ls ↢ r ∷ rs) = no λ ()

-- Returns the processed elements of a done belt.
finalize : ∀ {A B : Set} {load : ℕ}
  → ConveyorBelt A B load zero z≤n
  → Vec B load
finalize (ls ↢ []) = ls

