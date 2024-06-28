```agda
module Tutorial.NewLanguage where

open import Size using (∞)

open import Framework.Definitions
open import Framework.Variants using (Rose)
open import Framework.VariabilityLanguage
```

To define your own language, you must first define its (abstract syntax) as a data type.
For your type to be the syntax of a generic variability language,
the syntax must accept a set of atoms `A : 𝔸` as parameter:

```agda
data NewLang (A : 𝔸) : Set₁ where -- Why is this Set₁
  -- constructors go here
```

To form a variability language, your syntax also needs a configuration language. This might be just any type. For this example, we just call it `NewConf`.

```agda
NewConf : Set
NewConf = {!!}
```

With the configuration language, we can now define a semantics for variability of your language,
which must evaluate a term to a variant, given a configuration.
This means, to be compatible with our framework, the semantics must be of type:
```agda
V : 𝕍
V = Rose ∞

⟦_⟧ : ∀ {A : 𝔸} → NewLang A → NewConf → V A
-- ⟦_⟧ : 𝔼-Semantics V NewConf NewLang
⟦_⟧ = {!!}
```
where `V` is the type of variants. In our paper and for our language comparison, this type is always a rose tree `Rose ∞` (see [Variants.agda](src/Framework/Variants.agda)).

```agda
Lang : VariabilityLanguage V
Lang = ⟪ NewLang , NewConf , ⟦_⟧ ⟫
```
