# Completeness and Incompleteness of Variability Languages

## Module

```agda
open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
module Framework.Function.Properties.Completeness
  (O : Setoid 0ℓ 0ℓ)
  (I : Set)
  where
```

## Imports

```agda
open import Data.Product using (Σ-syntax)
open import Relation.Nullary.Negation  using (¬_)
open import Framework.FunctionLanguage
open import Data.IndexedSet O using (IndexedSet; _≅_)
open Setoid O
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
Complete : FunctionLanguage Carrier → Set
Complete ⟪ Expr , _ , ⟦_⟧ ⟫ =
  ∀ (m : IndexedSet I)
    ----------------------------------
  → Σ[ e ∈ Expr ] m ≅ ⟦ e ⟧
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : FunctionLanguage Carrier → Set
Incomplete L = ¬ (Complete L)
```
