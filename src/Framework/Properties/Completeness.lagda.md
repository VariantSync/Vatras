# Completeness and Incompleteness of Variability Languages

## Module

```agda
open import Framework.Definitions using (𝕍)
module Framework.Properties.Completeness (V : 𝕍) where
```

## Imports

```agda
open import Data.Product using (Σ-syntax)
open import Relation.Nullary.Negation using (¬_)
open import Framework.VariabilityLanguage
open import Framework.VariantGenerator V
open import Data.EqIndexedSet
```

## Definitions

A language is complete if for any element in its semantic domain, there exists an expression that denotes that element.
For variability languages, this means that given a variant map `m` there must exist an expression `e` that describes all variants in `m`.
In particular, for every variant `v` in `m`, there exists a configuration `c` that configures `e` to `v`.
```agda
Complete : VariabilityLanguage V → Set₁
Complete ⟪ E , _ , ⟦_⟧ ⟫ =
  ∀ {A} {n} (m : VariantGenerator A n)
    ----------------------
  → Σ[ e ∈ E A ] m ≅ ⟦ e ⟧
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : VariabilityLanguage V → Set₁
Incomplete L = ¬ (Complete L)
```
