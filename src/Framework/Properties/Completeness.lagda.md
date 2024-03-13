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
open import Framework.VariantMap V
open import Data.EqIndexedSet
```

## Definitions

Completeness is given iff for any set of variants `vs` (modeled as a list for convenience in Agda), there exists an expression `e` in the language `L` that describes all variants in `vs`.
In particular, for every variant `v` in `vs`, there exists a configuration `c` that configures `e` to `v`.
```agda
{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
Complete : VariabilityLanguage V → Set₁
Complete ⟪ E , _ , ⟦_⟧ ⟫ =
  ∀ {A} {n} (m : VMap A n)
    ----------------------
  → Σ[ e ∈ E A ] m ≅ ⟦ e ⟧
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : VariabilityLanguage V → Set₁
Incomplete L = ¬ (Complete L)
```
