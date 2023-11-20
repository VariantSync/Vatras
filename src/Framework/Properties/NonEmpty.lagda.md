# Checks that a variability language can describe at least one variant

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Framework.Properties.NonEmpty where
```

## Imports

```agda
open import Framework.Definitions using (VariabilityLanguage; Expression)
```

## Definitions

A variability language is not empty if there exists at least one configuration for each expression.
```agda
NonEmpty : ∀ {V S} (L : VariabilityLanguage V S) → Set₁
NonEmpty {S = S} L = ∀ {A} → Expression L A → S
```
