# Feature Traceability as Denotational Semantics

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module FeatureTrace where
```

## Imports

```agda
open import Data.Bool using (if_then_else_)
open import Data.List using (List; _∷_; []; map; concatMap)
open import Data.List.NonEmpty using (toList)

open import Size using (Size)

open import CC using (CC; Artifact; _⟨_⟩; Dimension; _dim-==_)
open import SemanticDomains
```

## Feature Traces in Choice Calculus

The semantics of a variation language is the set of variants it describes, or equivalently a generator that turns configurations into variants.
For some use cases, yet another formulation of semantics is of interest: feature traces - the knowledge where a certain feature is implemented.
As an example, we formulize feature traces for choice calculus:

```agda
CCFeatureTrace : Set → Set
CCFeatureTrace A = Dimension → List A

collect : {i : Size} {A : Set} → CC i A → List A
collect = {!!}

trace : {i : Size} {A : Set} → CC i A → CCFeatureTrace A
trace (Artifact a es) qD = {!!}
trace (D ⟨ es ⟩) qD = let les = toList es in
                     if D dim-== qD
                     then concatMap collect les
                     else concatMap (λ e → trace e D) les
```
Note: Not so easy: Just returning the artifacts is probably too naive because similar or equal elements in the object language cannot be distinguished anymore even though they trace to different features in different locations.
