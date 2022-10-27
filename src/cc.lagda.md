```agda
module cc where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.List
open import Agda.Builtin.String
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Extensionality
open import Functor
open import NonEmptyList
```

# Choice Calculus in Agda

Let's define core choices calculus as defined in Eric's phd thesis:
```agda
data Dimension : Set where
  Dim : String -> Dimension

data CC (A : Set) : Set where
  Artifact : A → List (CC A) → CC A 
  _⟨_⟩ : Dimension → NonEmptyList (CC A) → CC A
```

Let's build an example over strings. For this example, option calculus would be better because the subtrees aren't alternative but could be chosen in any combination. We know this from real-life experiments.
```agda
-- smart constructor for plain artifacts
leaf : {A : Set} → A → CC A
leaf a = Artifact a []

walk : CC String
walk = Dim "Ekko" ⟨ leaf "zoom" :! leaf "pee" ∷ leaf "poo" ∷ leaf "lick" ∷ [] ⟩
```

An algebaric decision diagram (ADD) is a choice calculus expression in which all leaves are artifacts.
We refer to a choice calculus expression whose abstract syntax is an ADD, as being in _product normal form_ (PNF):
In _A Formal Framework on Software Product Line Analyses_ and the 1997 ADD paper, ADDs are defined to be binary.
```agda
data ADD (A : Set) : Set where
  Product : A → ADD A -- ModelBase
  Choice : Dimension → ADD A → ADD A → ADD A -- ModelChoice, has a presence condition here instead of a dimension
```

To convert to product normal form, it is easier to first convert to binary normal form of choice calculus:
```
data BCC (A : Set) : Set where
  BArtifact : A → List (BCC A) → BCC A
  BChoice   : Dimension → BCC A → BCC A → BCC A

--bccAsCC : {A : Set} → BCC A → CC A
--bccAsCC (BArtifact a es) = Artifact a (map_l bccAsCC es)
--bccAsCC (BChoice d l r)  = d ⟨ (bccAsCC l) :! (bccAsCC r) ∷ [] ⟩
```
