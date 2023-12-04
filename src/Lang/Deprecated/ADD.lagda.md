# Algebraic Decision Diagrams

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.ADD where
```

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.List using ([])
open import Data.String using (String)
open import Size using (Size; ↑_; ∞)

open import Framework.Definitions using (𝕃; 𝔸; Variant; Semantics; VariabilityLanguage)
open import Framework.Annotation.Name using (Variable)
```

## Syntax

An algebraic decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ (FFSPL) and the 1997 ADD paper, ADDs are defined to be binary.

```agda
{-|
General algebraic decision diagrams that consists of choices that yield a value of type A.
-}
data ADD : 𝕃 where
  Terminal : ∀ {i : Size} {A : 𝔸}
    → A → ADD (↑ i) A -- ModelBase in FFSPL
  Choice : ∀ {i : Size} {A : 𝔸} →
    Variable → ADD i A → ADD i A → ADD (↑ i) A -- ModelChoice in FFSPL (has a presence condition here instead of a dimension)

{-|
Type of algebraic decision diagrams that describe variants.
When employing an ADD as a variability language, then it has to yield a variant.
-}
VADD : 𝕃
VADD i A = ADD i (Variant ∞ A)
```

## Semantics

```agda
{-|
Configurations denote a path in the tree by making a decision at each variable to select a certain terminal at the end.
-}
Configuration : Set
Configuration = Variable → Bool

-- ⟦_⟧ : ∀ {i : Size} {A : Set} → ADD i A → Configuration → Variant i A
⟦_⟧ : Semantics VADD Configuration
⟦ Terminal a ⟧ _   = a
⟦ Choice V l r ⟧ c = ⟦ if (c V) then l else r ⟧ c

VADDL : VariabilityLanguage
VADDL = record
  { expression = VADD
  ; configuration = Configuration
  ; semantics = ⟦_⟧
  }
```

## Sized Helper Functions

```agda
open import Util.SizeJuggle using (Bounded; Weaken; to-larger; to-max)

-- todo: move these boundes definition to BCC file
ADD-is-bounded : ∀ 𝔸 → Bounded
ADD-is-bounded A i = ADD i A

ADD-is-weakenable : ∀ {A : 𝔸} → Weaken (ADD-is-bounded A)
to-larger ADD-is-weakenable _ _ e = e
to-max    ADD-is-weakenable _ _ e = e
```

## Binary Decision Diagrams

Binary Decision Diagrams (BDDs) are ADDs in which we can only end at true or false.

```agda
BDD : Size → Set
BDD i = ADD i Bool
```

