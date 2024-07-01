```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Implementing your own variability language

This tutorial guides you through the process of defining your own
variability language within our framework.
It covers defining syntax, configurations, and semantics.

```agda
module Tutorial.A_NewLanguage where

open import Data.List using (List)
open import Size using (∞)

open import Framework.Definitions
open import Framework.Variants using (Rose)
open import Framework.VariabilityLanguage
```

To define your own language, you must first define its (abstract syntax) as a data type.
For your type to be the syntax of a generic variability language,
the syntax must accept a set of atoms `A : 𝔸` as parameter.
```agda
data MyLang : 𝔸 → Set₁ where
  -- example constructor for artifacts
  _-<_>_ : ∀ {A : 𝔸} → atoms A → List (MyLang A) → MyLang A
  -- more constructors go here
```
For examples, check the `Lang.All` module for an overview of the predefined languages.

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
In our paper and for the language comparisons implemented here, this type is often fixed to a rose tree `Rose ∞` (see [Variants.agda](src/Framework/Variants.agda)).
You can also change the type of variants produced (e.g., as in Gruler's language, which produces a `GrulerVariant`)
or even make your semantics generic in the type of variants.

Finally, we can define the full language as a triple of syntax, configuration language, and semantics.
```agda
MyVarLang : VariabilityLanguage V
MyVarLang = ⟪ MyLang , MyConfig , ⟦_⟧ ⟫
```
