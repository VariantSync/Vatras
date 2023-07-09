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
open import Framework.Definitions using (VariabilityLanguage; Expression; configuration)
```

## Definitions

A variability language is not empty if there exists at least one configuration for each expression.
```agda
NonEmpty : (L : VariabilityLanguage) → Set₁
NonEmpty L = ∀ {A} → Expression A L → configuration L
```

