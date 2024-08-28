```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Implementing your own variability language

This tutorial guides you through the process of defining your own
variability language within our framework.
It covers defining syntax, configurations, and semantics.

```agda
module Vatras.Tutorial.A_NewLanguage where

open import Data.List using (List)
open import Size using (∞)

open import Vatras.Framework.Definitions
open import Vatras.Framework.Variants using (Rose; _-<_>-)
open import Vatras.Framework.VariabilityLanguage
```

To define your own language, you must first define its (abstract syntax) as a data type.
For your type to be the syntax of a generic variability language,
the syntax must accept a set of atoms `A : 𝔸` as parameter.
```agda
open import Data.String

F : 𝔽
F = String

data MyLang : 𝔸 → Set₁ where
  -- constructors go here
```
Most variability languages use annotations `F` to refer to configuration options or features.
Such annotations are typically just plain names or propositional formulas.
Most variability languages formalized in this framework are parametric in the type `F : 𝔽` of annotations.
To keep the tutorial simple, we fix the annotations to strings here, so each string represents a name of a feature.
Nothing holds you back from coming back here later and replacing `String` with some other type (e.g., natural numbers ℕ or the abstract syntax of formulas).
This tutorial is intended to be played around with once you gathered some experience. 🙂
Feel free to use `F` in your definition or not if you do not need it.

If you are looking for some inspiration, you can try to follow the tutorial with the following syntax, inspired by the C preprocessor.
(If you want to use it, you just have to remove the first and last comment line, and also comment the definition above.)
```agda
{-
data MyLang : 𝔸 → Set₁ where
  -- artifacts
  artifact : ∀ {A : 𝔸} → atoms A → List (MyLang A) → MyLang A
  -- if-then-else-branch with negated condition
  #ifndef_#then_#else_ : ∀ {A : 𝔸} → F → MyLang A → MyLang A → MyLang A
-}
```

For more examples, check the `Lang.All` module for an overview of the predefined languages.

> It might be necessary to use sized types here for proving certain functions to terminate.
> For example, `CCC` is sized but `ADT` is not.

> It is necessary that the syntax is of type Set₁.
> The framework is not yet generic in universe levels, and the syntax must be of Set₁ because
> constructors are expected to be generic in the set of atoms as in the example constructor
> `_-<_>_` above.

To form a variability language, your syntax also needs a configuration language. This might be just any type.
Here we just call it `MyConfig`.
```agda
MyConfig : Set
MyConfig = {!!}
```

With the configuration language, we can now define a semantics for variability of your language,
which must evaluate a term to a variant, given a configuration.
This means, to be compatible with our framework, the semantics must be of type:
```agda
V : 𝕍
V = Rose ∞

⟦_⟧ : ∀ {A : 𝔸} → MyLang A → MyConfig → V A
⟦_⟧ = {!!}
```
where `V` is the type of variants.
In our paper and for the language comparisons implemented here, this type is often fixed to a rose tree `Rose ∞` (see [Variants.agda](../Framework/Variants.agda)).
You can also change the type of variants produced (e.g., as in Gruler's language, which produces a `GrulerVariant`) or even make your semantics generic in the type of variants.

In case you decided to go with the example C-preprocessor-inspired syntax above, try to find a reasonable semantics for it. (At the very bottom of this file, you can find an example solution for the semantics, which you can use to complete the remaining tutorial. We encourage you to try to find one your own semantics though. 🙂)

Finally, we can define the full language as a triple of syntax, configuration language, and semantics.
```agda
MyVarLang : VariabilityLanguage V
MyVarLang = ⟪ MyLang , MyConfig , ⟦_⟧ ⟫
```

    |
    |
    | scroll down for example semantics of example language above
    |
    |
    ↓
















## Some semantics for the CPP-inspired-language above

<details>
<summary>Spoiler Alert! Click me!</summary>

These are possible semantics for the proposed example language
above.

```agda
open import Data.Bool using (Bool; if_then_else_; not)
open Data.List using (map)

MyConfig' : Set
MyConfig' = F → Bool

{-
{-# TERMINATING #-}
⟦_⟧' : ∀ {A : 𝔸} → MyLang A → MyConfig' → V A
⟦ artifact a es ⟧' c = a -< map (λ e → ⟦ e ⟧' c) es >-
⟦ #ifndef cond #then t #else e ⟧' c =
  if not (c cond) -- negate because its #if_n_def
  then ⟦ t ⟧' c
  else ⟦ e ⟧' c
-}
```

We are using the `{-# TERMINATING -#}` flag here:
The reason is that it is not obvious to Agda's termination
checker that the input to the recursive call to the semantics
in the artifact case is smaller than the inpurt `artifact`.
One might prove termination here by using sized types (as we do
throughout the rest of the framework). To keep the tutorial
simple though, we just tell Agda here that the semantics are terminating
with an explicit pragma.

</details>
