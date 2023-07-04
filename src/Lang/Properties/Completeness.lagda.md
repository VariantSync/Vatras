# Completeness and Incompleteness of Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.Properties.Completeness where
```

## Imports

```agda
open import Data.Product using (Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Size using (∞)
open import Function using (_∘_)

open import Definitions

import Data.IndexedSet
private module ISet A = Data.IndexedSet (VariantSetoid ∞ A)
```

## Definitions

Completess is given iff for any set of variants `vs` (modelled as a list for convenience in Agda), there exists an expression `e` in the language `L` that describes all variants in `v`.
In particular, for every variant `v` in `vs`, there exists a configuration `c` that configures `e` to `v`.
```agda
Complete : VariabilityLanguage → Set₁
Complete L = ∀ {A n}
  → (vs : VSet A n)
    ----------------------------------
  → Σ[ e ∈ Expression A L ]
      (let open ISet A using (_≅_)
           ⟦_⟧ = semantics L ∘ get
        in vs ≅ ⟦ e ⟧)
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : VariabilityLanguage → Set₁
Incomplete L = ¬ (Complete L)
```
