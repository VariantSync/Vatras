module Axioms.Extensionality where

-- We use extensionality because
-- the semantic domain of variability languages is a function
-- and we want to prove these functions equivalent.

open import Axiom.Extensionality.Propositional using (Extensionality)

open import Data.List using (map)
open import Data.List.Properties using (map-cong)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl)

postulate
  extensionality : ∀ {a b} → Extensionality a b

≗→≡ : ∀ {A B : Set} {f g : A → B} → f ≗ g → f ≡ g
≗→≡ = extensionality

≡→≗ : ∀ {A B : Set} {f g : A → B} → f ≡ g → f ≗ g
≡→≗ f≡g rewrite f≡g = λ x → refl

map-cong-≗-≡ : ∀ {A B : Set} {f g : A → B} → f ≗ g → map f ≡ map g
map-cong-≗-≡ = ≗→≡ ∘ map-cong

map-cong-≡ : ∀ {A B : Set} {f g : A → B} → f ≡ g → map f ≡ map g
map-cong-≡ = map-cong-≗-≡ ∘ ≡→≗

