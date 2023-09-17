module Murder.Demo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)

-- record Player : Set where
--   constructor _murdered_people
--   field
--     name : String
--     kills : ℕ
-- open Player

-- make-player : String → Player
-- make-player = _murdered 0 people
make-player : ∀ {A : Set} → A → A
make-player x = x

-- kills++ : Player → Player
-- kills++ (x murdered i people) = x murdered (suc i) people

-- data Circle (A : Set) : Set where
--   _↻ : A → Circle A
--   _∷_ : A → Circle A → Circle A

Player : Set
Player = String

infixr 10 _↣_
data Game : Set where
  ↩ : Game -- \l
  _↣_ : Player → Game → Game -- \r->

# : Game → ℕ
# ↩ = zero
# (_ ↣ g) = suc (# g)

open import Data.Bool using (if_then_else_; false; true)
open Data.String using (_==_)
open Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Product using (∃-syntax; _,_)

infix 9 _∈_
data _∈_ (p : Player) : Game → Set where
  here : ∀ (g : Game)
           ----------
         → p ∈ p ↣ g

  there : ∀ {q g}
          → p ∈ g
            ---------
          → p ∈ q ↣ g

index-of : (p : Player) → (g : Game) → p ∈ g → ∃[ i ] (i ≤ # g)
index-of p (p ↣ g) (here g) = zero , z≤n
index-of p (q ↣ g) (there p∈g) with index-of p g p∈g
... | i , i≤#g = suc i , s≤s i≤#g

murder-at : (g : Game) → (i : ℕ) → (i ≤ # g) → Game
murder-at ↩ zero z≤n = ↩
murder-at (_ ↣ g) zero z≤n = g
murder-at (p ↣ g) (suc i) (s≤s i≤#g) = p ↣ murder-at g i i≤#g

murder : (p : Player) → (g : Game) → p ∈ g → Game
murder p g p∈g =
  let i , i≤#g = index-of p g p∈g
   in murder-at g i i≤#g

murder' : (target : String) → Game → Game
murder' _ ↩ = ↩
murder' target (victim? ↣ others) = if victim? == target
                                   then others
                                   else victim? ↣ murder' target others

-- winner : Game → Player
-- winner (x ↩) = x
-- winner (x ↣ g) = {!!}

open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

-- _∉_ : Player → Game → Set
-- p ∉ g = ¬ (p ∈ g)

infix 9 _∉_
data _∉_ (p : Player) : Game → Set where
  ∉-↩ : p ∉ ↩

  ∉-↣ : ∀ {q g}
        → ¬ (q == p) ≡ true
        → p ∉ g
          ----------
        → p ∉ q ↣ g

data WellFormed : Game → Set where
  ↩-wf : WellFormed ↩

  ↣-wf : ∀ {p g}
    → p ∉ g
      ------------------
    → WellFormed (p ↣ g)

data Finished : Game → Set where
  𝟘 : Finished ↩

  𝟙 : ∀ (p : Player)
        --------------
      → Finished (p ↣ ↩)

open import Data.Maybe using (Maybe; just; nothing)
winner : ∀ (g : Game) → Maybe Player
winner ↩ = nothing
winner (p ↣ ↩) = just p
winner (_ ↣ _ ↣ _) = nothing

-- murder target (x ↣ y ↣ rest) = murder' (last y rest) target (x ↣ y ↣ rest)
--   where murder' : Player → String → Game → Game
--         murder' killer target ↩ = ↩
--         murder' killer target (victim? ↣ others) = if name victim? == target
--                                                    then {!!}
--                                                    else {!!}

module Example where
  Thomas = make-player "Thomas"
  Sascha = make-player "Sascha"
  Tobias = make-player "Tobias"

  tsb : Game
  tsb = Thomas ↣ Sascha ↣ Tobias ↣ ↩

  _ : winner (murder' Thomas (murder' Sascha tsb)) ≡ just Tobias
  _ = refl

  _ : winner (murder' Tobias (murder' Sascha tsb)) ≡ just Thomas
  _ = refl

  _ : winner (murder Thomas (murder Sascha tsb {!!}) {!!}) ≡ just Tobias
  _ = refl

  -- _ : winner (murder Tobias (murder Sascha tsb)) ≡ Thomas
  -- _ = refl

open Eq.≡-Reasoning

murder'-idemp : ∀ p g → p ∉ g → murder' p g ≡ g
murder'-idemp _ ↩ _ = refl
murder'-idemp p (x ↣ g) (∉-↣ p≢q p∉g) with x == p
... | false = Eq.cong (x ↣_) (murder'-idemp p g p∉g)
... | true with p≢q refl
...        | ()

kill-comm : ∀ (g : Game) (p q : Player)
            → WellFormed g
              ---------------------------------------------
            → murder' p (murder' q g) ≡ murder' q (murder' p g)
kill-comm ↩ p q _ = refl
kill-comm (x ↣ xs) p q (↣-wf x∉xs) = {!!} --with x ≟ q with x==q
-- ... | false = {!!}
-- ... | true  = {!!}
