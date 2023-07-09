# Feature-Oriented Programming as a Variability Language

```agda
{-# OPTIONS --sized-types #-}

module Lang.FOP where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺)
open import Data.String using (String)

open import Size

open import Definitions
open import Util.Named
```

## Basic Definitions

A feature structure tree (FST) denotes the trace of a single feature.
It is a tree associated to a feature.
```agda
-- todo: Redefine as paths as done in the algebra by Apel

FSTName = String
Feature = String

data FSTNode (T : Set) : Size → Domain → Set where
  terminal : ∀ {i A}
    → FSTName → T → A → FSTNode T i A -- also has a name usually but we do not need it for the algebra
  inner : ∀ {i} {A}
    → FSTName → T → List⁺ (FSTNode T i A) → FSTNode T (↑ i) A

FST : (T : Set) → VarLang
FST T i A = Named (FSTNode T i A)

record Composer (T : Set) (A : Domain) : Set where
  constructor composing-via
  field
    compose : ∀ {i j} → FSTNode T i A → FSTNode T j A → FSTNode T ∞ A

record FOP (T : Set) (i : Size) (A : Domain) : Set where
  constructor [_+_]
  field
    base     : FST T i A
    features : List (FST T i A)
    composer : Composer T A

Configuration : Set
Configuration = Feature → Bool

toVariant : ∀ {T i A} → FSTNode T i A → Variant (↑ i) A
toVariant (terminal _ _ a) = leaf a
toVariant (inner _ _ children) = {!!}

⟦_⟧ : ∀ {T} → Semantics (FOP T) Configuration
⟦ [ b + [] ] (composing-via f) ⟧ c = {!!}
⟦ [ b + x ∷ xs ] (composing-via f) ⟧ c = {!!}

FOPL : Set → VariabilityLanguage
FOPL T = record
  { expression = FOP T
  ; configuration = Configuration
  ; semantics = ⟦_⟧
  }
```

