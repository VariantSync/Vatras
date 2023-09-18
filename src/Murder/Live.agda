module Murder.Live where

open import Data.Empty using (⊥)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Player : Set
Player = String

data Game : Set where
  empty : Game
  _must-kill_ : Player → Game → Game


















thomas : Player
thomas = "thomas"
sascha = "sascha"
sabrina = "sabrina"
