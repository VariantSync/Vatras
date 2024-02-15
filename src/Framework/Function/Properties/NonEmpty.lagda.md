# Checks that a variability language can describe at least one variant

## Module

```agda
module Framework.Function.Properties.NonEmpty where
```

## Imports

```agda
open import Framework.FunctionLanguage as FL using (FunctionLanguage)
open FL.FunctionLanguage
```

## Definitions

A variability language is not empty if there exists at least one configuration for each expression.
```agda
NonEmpty : ∀ {O} (L : FunctionLanguage O) → Set₁
NonEmpty L = ∀ {A} → Expression L A → Input L
```
