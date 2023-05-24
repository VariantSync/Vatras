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

```agda
-- record NonEmpty (L : VariabilityLanguage) : Set₁ where
--   private ⟦_⟧ = semantics L
--   field
--     describe : ∀ {i A} → Variant i A → expression L i A
--     describe-preserves : ∀ {i A}
--       → (v : Variant i A)
--         -----------------------------
--       → ∃[ c ] (v ≡ ⟦ describe v ⟧ c)
```

