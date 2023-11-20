# Completeness and Incompleteness of Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Framework.Properties.Completeness where
```

## Imports

```agda
open import Data.Product using (Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Size using (∞)
open import Function using (_∘_)

open import Framework.Variant
open import Framework.Definitions

import Data.IndexedSet
```

## Definitions

Completeness is given iff for any set of variants `vs` (modeled as a list for convenience in Agda), there exists an expression `e` in the language `L` that describes all variants in `vs`.
In particular, for every variant `v` in `vs`, there exists a configuration `c` that configures `e` to `v`.
```agda
Complete : ∀ {V S} → VariabilityLanguage V S → Set₁
Complete {V} (syn Expr with-sem ⟦_⟧) = ∀ {A n}
  → (vs : VMap V A n)
    ----------------------------------
  → Σ[ e ∈ Expr A ]
      let open IVSet V A using (_≅_)
        in vs ≅ ⟦ e ⟧
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : ∀ {V S} → VariabilityLanguage V S → Set₁
Incomplete L = ¬ (Complete L)
```
