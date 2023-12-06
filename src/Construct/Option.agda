module Construct.Option where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; nothing; just)
open import Level using (_⊔_)

record Option {ℓ₁ ℓ₂} (Q : Set ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _❲_❳
  field
    name  : Q
    child : A

Config : ∀ {ℓ₁} (Q : Set ℓ₁) → Set ℓ₁
Config Q = Q → Bool

OptionSemantics : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Option Q A → Config Q → Maybe A
OptionSemantics (O ❲ e ❳) c = if c O then just e else nothing

WOptionSemantics : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → (A → A) → Option Q A → Config Q → A
WOptionSemantics nest (O ❲ e ❳) c = if c O then e else nest e

record Noption {ℓ₁ ℓ₂} (Q : Set ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor ¬_❲_❳
  field
    name  : Q
    child : A

NoptionSemantics : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Noption Q A → Config Q → Maybe A
NoptionSemantics (¬ O ❲ e ❳) c = if c O then nothing else just e

WNoptionSemantics : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → (A → A) → Noption Q A → Config Q → A
WNoptionSemantics nest (¬ O ❲ e ❳) c = if c O then nest e else e
