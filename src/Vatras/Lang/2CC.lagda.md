# Binary Choice Calculus

## Module

```agda
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; 𝔼; ℂ)
module Vatras.Lang.2CC (Dimension : 𝔽) where
```

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.List as List using (List)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage using (𝔼-Semantics; VariabilityLanguage; ⟪_,_,_⟫)
```

## Syntax

In the following we formalize the binary normal form for choice calculus.
We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system.
A binary choice calculus expression is either an artifact `a -< es >-` (just as in [rose trees](../Framework/Variants.agda))
or a binary choice `D ⟨ l , r ⟩` between two sub-expressions `l` and `r`, where the dimension `D` gives the choice a name
to identify the choice upon configuration.
Dimensions `D` can be of any given type `Dimension : 𝔽`.
```agda
data 2CC : Size → 𝔼 where
   _-<_>- : ∀ {i A} → atoms A → List (2CC i A) → 2CC (↑ i) A
   _⟨_,_⟩ : ∀ {i A} → Dimension → 2CC i A → 2CC i A → 2CC (↑ i) A
```

## Semantics

The semantics of binary normal form is essentially the same as for core choice calculus.
We define the semantics explicitly though because specializing the semantics to the binary case gives rise to simplifications and transformation rules.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also possible but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Configuration : ℂ
Configuration = Dimension → Bool

⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics (Rose ∞) Configuration (2CC i)
⟦ a -< cs >-  ⟧ c = a V.-< List.map (λ e → ⟦ e ⟧ c) cs >-
⟦ D ⟨ l , r ⟩ ⟧ c =
  if c D
  then ⟦ l ⟧ c
  else ⟦ r ⟧ c

2CCL : ∀ {i : Size} → VariabilityLanguage (Rose ∞)
2CCL {i} = ⟪ 2CC i , Configuration , ⟦_⟧ ⟫
```
