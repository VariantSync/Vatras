# Checks that a variability language can describe at least one variant

## Module

```agda
module Framework.Properties.NonEmpty where
```

## Imports

```agda
open import Framework.VariabilityLanguage using (VariabilityLanguage; Expression; Config)
```

## Definitions

A variability language is not empty if there exists at least one configuration for each expression.
```agda
NonEmpty : ∀ (L : VariabilityLanguage) → Set₁
NonEmpty L = ∀ {A} → Expression L A → Config L
```
