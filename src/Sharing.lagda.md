# Ideas on sharing

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Sharing where
```

## Imports

```agda
open import Data.Product using (Σ-syntax)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Size using (Size)

open import Framework.Definitions using (𝔸; Variant; Artifactᵥ)
```

## Formalizing the Sharing Assumption

The sharing assumption for a variable / configurable system states that all described variants share some of their structure, meaning that they are similar in some way.
To formalize the sharing assumption to use it in our proofs, we have to define what it means for variants to share similarities.

As a first, more strict definition, we observe that variants have sharing if all variants have the same root element:
```agda
has-root : ∀ {i : Size} {A : 𝔸} → A → Variant i A → Set
has-root a (Artifactᵥ b es) = a ≡ b

root-sharing : ∀ {i : Size} {A : 𝔸} → List (Variant i A) → Set
root-sharing {A = A} vs = Σ[ a ∈ A ] (All (has-root a) vs)
```

Todo: Prove that OC is complete when assuming `root-sharing`.

