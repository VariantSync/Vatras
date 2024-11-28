```agda
open import Vatras.Framework.Definitions
module Vatras.Framework.Relation.Syntax (V : 𝕍) where

open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Relation.Expression V
```

Let $L$, $M$ be two languages.
Let $l \in L$.
If $\forall m \in M$
that is semantically equivalent to l,
$|l|_a < |m|_a$
then $M$ must be less expressive than $L$ because there is just no expression in $M$ with a smarter encoding. But what about the choice of $l$?
```agda
open import Data.Nat using (ℕ; _≤_)

record MeasurableVariabilityLanguage (V : 𝕍) : Set₂ where
  constructor [_,_]
  field
    Language : VariabilityLanguage V
    count-atoms : ∀ {A} → Expression Language A → ℕ
open MeasurableVariabilityLanguage public

_⊵_ : ∀ (L M : MeasurableVariabilityLanguage V) → Set₁ --\succeq
[ L , ∥_∥ₗ ] ⊵ [ M , ∥_∥ₘ ] =
  ∀ {A : 𝔸} (l : Expression L A) (m : Expression M A)
  → L , M ⊢ l ≣ m
  → ∥ l ∥ₗ ≤ ∥ m ∥ₘ
```

