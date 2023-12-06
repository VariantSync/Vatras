# Completeness and Incompleteness of Variability Languages

## Module

```agda
open import Relation.Binary using (Setoid)
open import Level using (0ℓ)
open import Data.Product using (Σ; Σ-syntax)
module Framework.Function.Properties.Completeness
  (O : Set → Setoid 0ℓ 0ℓ)
  (P : Set)
  (I : P → Set)
  where
```

## Imports

```agda
open import Relation.Nullary.Negation  using (¬_)
open import Function using (_∘_)
open import Framework.FunctionLanguage
import Data.IndexedSet
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
Complete : FunctionLanguage (Setoid.Carrier ∘ O) → Set₁
Complete ⟪ Expr , _ , ⟦_⟧ ⟫ =
  ∀ {A} → let open Data.IndexedSet (O A) in
  ∀ {p} → (m : IndexedSet (I p))
    ----------------------------------
  → Σ[ e ∈ Expr A ] m ≅ ⟦ e ⟧
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : FunctionLanguage (Setoid.Carrier ∘ O) → Set₁
Incomplete L = ¬ (Complete L)
```
