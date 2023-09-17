
module Murder.Live where

open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Player : Set
Player = String

data Game : Set where
  ↩ : Game
  _↣_ : Player → Game → Game
infixr 10 _↣_

thomas : Player
thomas = "thomas"
sascha = "sascha"
tobias = "tobias"

example : Game
example = thomas ↣ sascha ↣ tobias ↣ ↩
