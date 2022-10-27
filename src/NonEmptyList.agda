open import Agda.Builtin.List
open import Functor

data NonEmptyList {a} (A : Set a) : Set a where
  _:!_ : A → List A → NonEmptyList A
infixr 5 _:!_

map_nelist : ∀ {A B : Set} → (A → B) → NonEmptyList A → NonEmptyList B
map_nelist f (x :! xs) = (f x) :! (map_list f xs)
