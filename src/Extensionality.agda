import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

id : {A : Set} → A → A
id x = x

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
