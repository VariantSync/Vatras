module Data.ConveyorBelt where

open import Data.List using (List; []; _∷_)
open import Data.ReversedList using (ReversedList; []; _∷_; toList)

record ConveyorBelt (A B : Set) : Set where
   constructor _↢_ -- \l->
   field
     processed   : ReversedList B
     unprocessed : List A
open ConveyorBelt public
infix 4 _↢_

putOnBelt : ∀ {A B : Set} → List A → ConveyorBelt A B
putOnBelt l = record
  { processed   = []
  ; unprocessed = l
  }

step : ∀ {A B : Set} → (A → B) → ConveyorBelt A B → ConveyorBelt A B
step _ z@(_ ↢ [])    = z
step f (ls ↢ r ∷ rs) = ls ∷ f r ↢ rs

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Relation.Nullary.Decidable using (Dec; yes; no; True)
open import Data.Unit.Base using (tt)

-- True iff nothing is left to process, false otherwise.
done : ∀ {A B : Set} → (belt : ConveyorBelt A B) → Dec (unprocessed belt ≡ [])
done (processed ↢ []) = yes refl
done (processed ↢ u ∷ unprocessed) = no λ ()

-- Returns the processed elements of a done belt.
finalize : ∀ {A B : Set} → (belt : ConveyorBelt A B) → {True (done belt)} → List B
finalize (ls ↢ []) = toList ls
