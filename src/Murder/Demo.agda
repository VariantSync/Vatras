module Murder.Demo where

open import Data.Empty using (⊥)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Player : Set
Player = String

data Game : Set where
  ↺ : Game -- \l
  _➵_ : (p : Player) → (g : Game) → Game -- \r-> or (\8< for ✂), (\r for ⇀), (\r for ➵)
infixr 10 _➵_

thomas : Player
thomas = "thomas"
sascha = "sascha"
sabrina = "sabrina"

example : Game
example = thomas ➵ sascha ➵ sabrina ➵ ↺

winner : Game → Maybe Player
winner ↺ = nothing
winner (p ➵ ↺) = just p
winner (_ ➵ _ ➵ _) = nothing

_ : winner example ≡ nothing
_ = refl

_ : winner (sascha ➵ ↺) ≡ just sascha
_ = refl

data Won : Game → Set where
  wins : ∀ (p : Player)
         --------------
       → Won (p ➵ ↺)

data Finished : Game → Set where
  𝟘 : Finished ↺

  𝟙 : ∀ (p : Player)
        --------------
      → Finished (p ➵ ↺)

-- Only finished games can be won.
Won⇒Finished : ∀ (g : Game) → Won g → Finished g
Won⇒Finished .(p ➵ ↺) (wins p) = 𝟙 p

open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)

¬Finished⇒¬Won : ∀ (g : Game) → ¬ (Finished g) → ¬ (Won g)
¬Finished⇒¬Won ↺ g ()
¬Finished⇒¬Won (p ➵ ↺) unfinished (wins .p) = contradiction (𝟙 p) unfinished
-- ¬Finished⇒¬Won (p ➵ ↺) unfinished (wins .p) = unfinished (𝟙 p)
¬Finished⇒¬Won (p ➵ q ➵ g) unfinished ()

¬Finished⇒¬Won' : ∀ (g : Game) → ¬ (Finished g) → ¬ (Won g)
¬Finished⇒¬Won' g = contraposition (Won⇒Finished g)

-- Every won game has a winner.
winner' : ∀ (g : Game) → Won g → Player
winner' .(p ➵ ↺) (wins p) = p

-- simple murder
open Data.String using (_==_)
open import Data.Bool using (if_then_else_)

murder : (target : String) → Game → Game
murder _ ↺ = ↺
murder target (victim? ➵ others) = if victim? == target
                                    then others
                                    else victim? ➵ murder target others

_ : winner example ≡ nothing
_ = refl

_ : winner (murder thomas (murder sascha example)) ≡ just sabrina
_ = refl

_ : winner (murder sabrina (murder sascha example)) ≡ just thomas
_ = refl

-- sophisticated murder
-- murder' : (p : Player) → (g : Game) → p ∈ g → Game

infix 9 _∈_
data _∈_ (p : Player) : Game → Set where
  here  : ∀ {g}
            ------------
          → p ∈ (p ➵ g)

  there : ∀ {q g}
          → p ∈ g
            ------------
          → p ∈ (q ➵ g)

_ : thomas ∈ example
_ = here

s∈e : sascha ∈ example
s∈e = there here

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (∃-syntax; _,_)

#players : Game → ℕ
#players ↺ = zero
#players (_ ➵ g) = suc (#players g)

index-of : (p : Player) → (g : Game) → p ∈ g → ∃[ i ] (i ≤ #players g)
index-of p (p ➵ g) here = zero , z≤n
index-of p (q ➵ g) (there p∈g) with index-of p g p∈g
... | i , i≤#g = suc i , s≤s i≤#g

_ : index-of sascha example s∈e ≡ (1 , s≤s z≤n)
_ = refl

murder-at : (g : Game) → (i : ℕ) → (i ≤ #players g) → Game
murder-at ↺ zero z≤n = ↺
murder-at (_ ➵ g) zero z≤n = g
murder-at (p ➵ g) (suc i) (s≤s i≤#g) = p ➵ murder-at g i i≤#g

murder' : (p : Player) → (g : Game) → p ∈ g → Game
murder' p g p∈g =
  let i , i≤#g = index-of p g p∈g
   in murder-at g i i≤#g

_ : winner (murder' thomas (murder' sascha example s∈e) here) ≡ just sabrina
_ = refl

----- WHAT ELSE
{-
- equivalence of games
- murder' reduces game size by 1
- murder' kills no other person that is not the target
- add kill count
- formalize murder' as denotational semantics!
  - Denotation of a game g is a function that takes a list of kill targets and produces a sub game (or direct winner)
-}

----- MIND BLOWERS
{-
- ≡ is a type
- ≡-Reasoning
-}

----- BONUS

-- open Eq.≡-Reasoning

_∉_ : Player → Game → Set
p ∉ g = ¬ (p ∈ g)

paul∉example : "Paul" ∉ example
paul∉example (there (there (there ())))

-- A game should not contain duplicate players
-- Otherwise, murder is not commutative.
data WellFormed : Game → Set where
  ↺-wf : WellFormed ↺

  ➵-wf : ∀ {p g}
    → p ∉ g
    → WellFormed g
      ------------------
    → WellFormed (p ➵ g)

