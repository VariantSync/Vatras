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
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import SemanticDomain using (Variant; Artifactᵥ)
open import Translation.Translation using (Domain)

open import Util.Existence using (∃-syntax-with-type)
```

## Formalizing the Sharing Assumption

The sharing assumption for a variable / configurable system states that all described variants share some of their structure, meaning that they are similar in some way.
To formalize the sharing assumption to use it in our proofs, we have to define what it means for variants to share similarities.

As a first, more strict definition, we observe that variants have sharing if all variants have the same root element:
```agda
has-root : ∀ {A : Domain} → A → Variant A → Set
has-root a (Artifactᵥ b es) = a ≡ b

root-sharing : ∀ {A : Domain} → List (Variant A) → Set
root-sharing {A} vs = ∃[ a ∈ A ] (All (has-root a) vs)
```

Todo: Prove that OC is complete when assuming `root-sharing`.

