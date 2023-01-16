# Variation Trees

```agda
module Lang.VariationTree where

open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl)
open import Data.List.Relation.Unary.All using (All)

ID : Set
ID = ℕ

infix 4 _∈_
data _∈_ : {A : Set} → A → List A → Set where
  here : ∀ {A : Set} {l : List A} {x : A}
      ---------------------
    → x ∈ x ∷ l

  there : ∀ {A : Set} {l : List A} {x y : A}
    → x ≢ y
    → x ∈ l
      ---------------------
    → x ∈ y ∷ l

data HasNeutral (A : Set) : Set where
  neutral : A → HasNeutral A

data VTLabel (A F : Set) : Set where
  ArtifactLabel : A → VTLabel A F
  MappingLabel : F → VTLabel A F
  ElseLabel : VTLabel A F

record VTNode (A F : Set) : Set where
  constructor node
  field
    id : ID
    label : VTLabel A F
open VTNode

root : {A F : Set} → HasNeutral F → VTNode A F
root (neutral e) = node 0 (MappingLabel e)

VTEdges : Set → Set → Set
VTEdges A F = List (VTNode A F × VTNode A F)

data IsDefined {A B : Set} : List (A × B) → A → Set where
  -- TODO Here and there

data TotalFunction {A B : Set} : List (A × B) → List A → Set where
  

record VariationTree (A F : Set) : Set where
  field
    nodes : List (VTNode A F)
    edges : VTEdges A F
    -- Well-formedness criteria
    f-neutral : HasNeutral F
    hasRoot : root f-neutral ∈ nodes
    --rootHasNoParent : 
    exactlyOneParent : TotalFunction edges nodes

data VTExpr (A F : Set) : Set where
  Artifact : A → List (VTExpr A F) → VTExpr A F
  If_Then : F → List (VTExpr A F) → VTExpr A F
  If_Then_Else : F → List (VTExpr A F) → List (VTExpr A F) → VTExpr A F

{-
data WF : {A F : Set} → VariationTree A F → Set where
-}
```
