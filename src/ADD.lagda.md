# Algebraic Decision Diagrams

## Module

```agda
module ADD where
```

## Imports

```agda
open import Data.Bool using (Bool)
open import Data.String.Base using (String)

--open import CC using (Dimension)
```

## Definition

An algebraic decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ (FFSPL) and the 1997 ADD paper, ADDs are defined to be binary.

```agda
Dimension : Set
Dimension = String

-- TODO: Make sized
data ADD (A : Set) : Set where
  Terminal : A → ADD A -- ModelBase in FFSPL
  Choice : Dimension → ADD A → ADD A → ADD A -- ModelChoice in FFSPL (has a presence condition here instead of a dimension)

-- BDDs are ADDs in which we can only end at true or false.
BDD : Set
BDD = ADD Bool
```
