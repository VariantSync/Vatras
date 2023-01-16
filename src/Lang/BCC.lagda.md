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
open import Axioms.Extensionality using (extensionality)
open import Lang.Annotation.Dimension using (Dimension)
open import Translation.Translation
  -- Names
  using (VarLang; ConfLang; Domain; Semantics)
  -- Relations of expression in a variability language
  using (_,_⊢_≈_)
open import SemanticDomain using (Variant; Artifactᵥ)
```

## Syntax

In the following we formalize the binary normal forms for choice calculus. We express a normal form as a new data type such that a conversion of a choice calculus expression is proven in the type system. Our goal is to prove that every choice calculus expression can be expressed as a variant-equivalent choice calculus expression in which every choice is binary.

```agda
data BCC : VarLang where
  Artifact : {i : Size} {j : Size< i} {A : Domain} →
    A → List (BCC j A) → BCC i A
  _⟨_,_⟩ : {i : Size} {j : Size< i} {A : Domain} →
    Dimension → BCC j A → BCC j A → BCC i A
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
Tag : Set
Tag = Bool

left  = true
right = false

Configuration : ConfLang
Configuration = Dimension → Tag

⟦_⟧ : Semantics BCC Configuration
⟦ Artifact a es ⟧ c = Artifactᵥ a (mapl (flip ⟦_⟧ c) es)
⟦ D ⟨ l , r ⟩ ⟧ c = ⟦ if (c D) then l else r ⟧ c
```

## Properties

Some transformation rules:
```agda
open import Util.AuxProofs using (if-idemp; if-cong)
open Data.List using ([_])

cc-idemp : ∀ {i : Size} {A : Set} {D : Dimension} {e : BCC i A}
    -----------------------------
  → BCC , ⟦_⟧ ⊢ D ⟨ e , e ⟩ ≈ e
cc-idemp {i} {A} {D} {e} = extensionality (λ c →
  ⟦ D ⟨ e , e ⟩ ⟧ c             ≡⟨⟩
  ⟦ if (c D) then e else e ⟧ c  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧ c) (if-idemp (c D)) ⟩
  ⟦ e ⟧ c                       ∎)

-- Sharing of equal prefixes in sub-expressions
-- Note: This is hard to generalize to Artifact's with multiple children because
--       we cannot put these children below the choice directly. Instead we would have
--       to introduce empty artifacts that do not represent expression in the object language but
--       rather containers in the meta-language. Maybe it would make sense to generalize choice
--       calculus to have lists of lists of children in choices instead of exactly one subtree per alternative.
cc-prefix-sharing : ∀ {i : Size} {A : Set} {D : Dimension} {a : A} {x y : BCC i A}
  → BCC , ⟦_⟧ ⊢ D ⟨ Artifact a [ x ] , Artifact a [ y ] ⟩ ≈ Artifact a [ D ⟨ x , y ⟩ ]
cc-prefix-sharing {_} {_} {D} {a} {x} {y} = extensionality (λ c →
  begin
    ⟦ D ⟨ Artifact a [ x ] , Artifact a [ y ] ⟩ ⟧ c
  ≡⟨⟩
    ⟦ if (c D) then (Artifact a [ x ]) else (Artifact a [ y ] ) ⟧ c
  ≡⟨ Eq.cong (λ eq → ⟦ eq ⟧ c) (if-cong (c D) (λ {v → Artifact a [ v ]}) ) ⟩
    ⟦ Artifact a [ if (c D) then x else y ] ⟧ c
  ≡⟨⟩
    ⟦ Artifact a [ D ⟨ x , y ⟩ ] ⟧ c
  ∎)
```

## Utility

```agda
open Data.List using (concatMap) renaming (_++_ to _++l_)

-- get all dimensions used in a binary CC expression
dims : ∀ {i : Size} {A : Set} → BCC i A → List Dimension
dims (Artifact _ es) = concatMap dims es
dims (D ⟨ l , r ⟩) = D ∷ (dims l ++l dims r)
```

## Show

```agda
open import Data.String using (String; _++_)

show : ∀ {i : Size} → BCC i String → String
show (Artifact a []) = a
show (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl show es)) ++ ">-"
show (D ⟨ l , r ⟩) = D ++ "<" ++ (show l) ++ ", " ++ (show r) ++ ">"
```
