import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq using (_≗_)

open import Function using (_∘_; id)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

eta-equivalence : ∀ {A B : Set} {f : A → B}
    ---------------
  → f ≡ λ {x → f x}
eta-equivalence = refl

≗→≡ : ∀ {A B : Set} {f g : A → B} → f ≗ g → f ≡ g
≗→≡ f≗g = extensionality f≗g

≡→≗ : ∀ {A B : Set} {f g : A → B} → f ≡ g → f ≗ g
≡→≗ f≡g rewrite f≡g = λ x → refl

open import Function.Base using (_∘_)
open import Data.List using (map)
open import Data.List.Properties using (map-cong)

map-cong-≗-≡ : ∀ {A B : Set} {f g : A → B} → f ≗ g → map f ≡ map g
map-cong-≗-≡ f≗g = ≗→≡ (map-cong f≗g)

map-cong-≡ : ∀ {A B : Set} {f g : A → B} → f ≡ g → map f ≡ map g
map-cong-≡ = map-cong-≗-≡ ∘ ≡→≗

_embeds-via_ : ∀ {A B : Set}
  → (to   : A → B)
  → (from : B → A)
    --------------
  → Set
to embeds-via from = from ∘ to ≗ id
