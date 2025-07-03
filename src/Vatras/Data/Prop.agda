module Vatras.Data.Prop where

open import Data.Bool as Bool using (Bool)

data Prop (F : Set) : Set where
  true  : Prop F
  false : Prop F
  var   : F → Prop F
  ¬_    : Prop F → Prop F
  _∧_   : Prop F → Prop F → Prop F

infix 24 var
infix 23 ¬_
infix 22 _∧_

_∨_ : ∀ {F} → Prop F → Prop F → Prop F
a ∨ b = ¬ (¬ a ∧ ¬ b)

_⇒_ : ∀ {F} → Prop F → Prop F → Prop F
a ⇒ b = ¬ a ∨ b

_⇔_ : ∀ {F} → Prop F → Prop F → Prop F
a ⇔ b = (a ⇒ b) ∧ (b ⇒ a)

Assignment : Set → Set
Assignment F = F → Bool

eval : ∀ {F} → Prop F → Assignment F → Bool
eval true    _ = Bool.true
eval false   _ = Bool.false
eval (var p) c = c p
eval (¬ p)   c = Bool.not (eval p c)
eval (p ∧ q) c = (eval p c) Bool.∧ (eval q c)

