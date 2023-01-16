# Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.BCC where
```

## Imports

```agda
-- stdlib
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List
  using (List; []; _∷_; lookup)
  renaming (map to mapl)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Function
  using (flip)
open import Size
  using (Size; Size<_)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- own modules
open import Extensionality using (extensionality)
open import Lang.Annotation.Dimension using (Dimension)
open import Translation.Translation
  -- Names
  using (VarLang; ConfLang; Domain; Semantics)
  -- Relations of expression in a variability language
  using (_,_⊢_≈_)
open import SemanticDomains using (Variant; Artifactᵥ)
```

## Syntax

In the following we formalize the binary normal forms for choice calculus. We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system. Our goal is to prove that every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.

```agda
data CC₂ : VarLang where
  Artifact₂ : {i : Size} {j : Size< i} {A : Domain} →
    A → List (CC₂ j A) → CC₂ i A
  _⟨_,_⟩₂ : {i : Size} {j : Size< i} {A : Domain} →
    Dimension → CC₂ j A → CC₂ j A → CC₂ i A
```

## Semantics

The semantics of binary normal form is essentially the same as for n-ary choice calculus.
We define the semantics explicitly though because of two reasons:

1. Specializing the semantics to the binary case gives rise to further simplifications and transformation rules.
2. Defining binary semantics explicitly allows us to prove that a conversion from and to binary normal form is semantics preserving.

To define the semantics of the binary normal form, we also introduce new binary tags because configurations now have to choose from two alternatives.
Doing so is isomorphic to choosing a boolean value (i.e., being a predicate).
We define `true` to mean choosing the left alternative and `false` to choose the right alternative.
Defining it the other way around is also ok but we have to pick one definition and stay consistent.
We choose this order to follow the known _if c then a else b_ pattern where the evaluation of a condition _c_ to true means choosing the then-branch, which is the left one.
```agda
Tag₂ : Set
Tag₂ = Bool

left  = true
right = false

Configuration₂ : ConfLang
Configuration₂ = Dimension → Tag₂

⟦_⟧₂ : Semantics CC₂ Configuration₂
⟦ Artifact₂ a es ⟧₂ c = Artifactᵥ a (mapl (flip ⟦_⟧₂ c) es)
⟦ D ⟨ l , r ⟩₂ ⟧₂ c = ⟦ if (c D) then l else r ⟧₂ c
```

## Properties

Some transformation rules:
```agda
open import AuxProofs using (if-idemp; if-cong)
open Data.List using ([_])

cc₂-idemp : ∀ {i : Size} {A : Set} {D : Dimension} {e : CC₂ i A}
    -----------------------------
  → CC₂ , ⟦_⟧₂ ⊢ D ⟨ e , e ⟩₂ ≈ e
cc₂-idemp {i} {A} {D} {e} = extensionality (λ c →
  ⟦ D ⟨ e , e ⟩₂ ⟧₂ c             ≡⟨⟩
  ⟦ if (c D) then e else e ⟧₂ c  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧₂ c) (if-idemp (c D)) ⟩
  ⟦ e ⟧₂ c                       ∎)

-- Sharing of equal prefixes in sub-expressions
-- Note: This is hard to generalize to Artifact₂'s with multiple children because
--       we cannot put these children below the choice directly. Instead we would have
--       to introduce empty artifacts that do not represent expression in the object language but
--       rather containers in the meta-language. Maybe it would make sense to generalize choice
--       calculus to have lists of lists of children in choices instead of exactly one subtree per alternative.
cc₂-prefix-sharing : ∀ {i : Size} {A : Set} {D : Dimension} {a : A} {x y : CC₂ i A}
  → CC₂ , ⟦_⟧₂ ⊢ D ⟨ Artifact₂ a [ x ] , Artifact₂ a [ y ] ⟩₂ ≈ Artifact₂ a [ D ⟨ x , y ⟩₂ ]
cc₂-prefix-sharing {_} {_} {D} {a} {x} {y} = extensionality (λ c →
  begin
    ⟦ D ⟨ Artifact₂ a [ x ] , Artifact₂ a [ y ] ⟩₂ ⟧₂ c
  ≡⟨⟩
    ⟦ if (c D) then (Artifact₂ a [ x ]) else (Artifact₂ a [ y ] ) ⟧₂ c
  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧₂ c) (if-cong (c D) (λ {v → Artifact₂ a [ v ]}) ) ⟩
    ⟦ Artifact₂ a [ if (c D) then x else y ] ⟧₂ c
  ≡⟨⟩
    ⟦ Artifact₂ a [ D ⟨ x , y ⟩₂ ] ⟧₂ c
  ∎)
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → CC₂ i A → List Dimension
dims (Artifact₂ _ es) = concatMap dims es
dims (D ⟨ l , r ⟩₂) = D ∷ (dims l ++l dims r)
```

## Show

```agda
open import Data.String using (String; _++_)

show : ∀ {i : Size} → CC₂ i String → String
show (Artifact₂ a []) = a
show (Artifact₂ a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl show es)) ++ ">-"
show (D ⟨ l , r ⟩₂) = D ++ "<" ++ (show l) ++ ", " ++ (show r) ++ ">"
```
