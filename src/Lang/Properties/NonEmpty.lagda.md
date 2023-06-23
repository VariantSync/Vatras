# Checks that a variability language can describe at least one variant

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.Properties.NonEmpty where
```

## Imports

```agda
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (∞)

open import Definitions
```

## Definitions

A variability language is not empty if there exists at least one configuration for each expression.
```agda
NonEmpty : (L : VariabilityLanguage) → Set₁
NonEmpty L = ∀ {A} → Expression A L → configuration L
```

