# Algebraic Decision Diagrams in Agda

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module ADD where
```

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.List using ([])
open import Data.String using (String)
open import Size using (Size; Size<_)

open import SemanticDomains using (Variant; Artifactᵥ)
```

## Algebraic Decision Diagrams

An algebraic decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ (FFSPL) and the 1997 ADD paper, ADDs are defined to be binary.

### Syntax

```agda
Variable : Set
Variable = String

data ADD (i : Size) (A : Set) : Set where
  Terminal : A → ADD i A -- ModelBase in FFSPL
  Choice : ∀ {j : Size< i} →
    Variable → ADD j A → ADD j A → ADD i A -- ModelChoice in FFSPL (has a presence condition here instead of a dimension)
```

### Semantics

```agda
{-|
Configurations denote a path in the tree by making a decision at each variable to select a certain terminal at the end.
-}
Configuration : Set
Configuration = Variable → Bool

⟦_⟧ : ∀ {i : Size} {A : Set} → ADD i A → Configuration → Variant A
⟦ Terminal a ⟧ _   = Artifactᵥ a []
⟦ Choice V l r ⟧ c = ⟦ if (c V) then l else r ⟧ c
```

### Translation to Binary Choice Calculus

TODO: Import CC once it has no more holes in it.
TODO: Prove variant-preserving equivalence.

## Binary Decision Diagrams

Binary Decision Diagrams (BDDs) are ADDs in which we can only end at true or false.

```agda
BDD : Size → Set
BDD i = ADD i Bool
```

Thus, a translation from BDDs to ADDs exists trivially.
Yet, the inverse does not apply:
Not every ADD can be translated to a BDD.
This is proven by the fact that not every data type (e.g., natural numbers `ℕ`) is isomorphic to `Bool` and thus an ADD can describe a set of variants that cannot be described by any BDD.

