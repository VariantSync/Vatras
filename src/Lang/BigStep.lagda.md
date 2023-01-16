# Alternative Formulation of Semantics of BCC as Transition Relations (Currently Playground)

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.BigStep where
```

## Imports
```agda
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Size using (Size; ↑_; ∞)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl)

-- Imports of own modules
open import Lang.Annotation.Dimension using (Dimension; _≟_)
open import Lang.BCC using (Tag₂; CC₂; Artifact₂; _⟨_,_⟩₂; left; right)
open import SemanticDomain using (Variant; Artifactᵥ)
open import Extensionality
  using (extensionality)

open import Data.List.Relation.Unary.All using (All; reduce; []; _∷_)

open import Relation.Nullary.Decidable using (False; toWitnessFalse)
```

## Binary Choice Calculus

Configurations as lists instead of functions so we can inspect them:
```agda
infixl 5 _and_↦_
data Assignment (L R : Set) : Set where
  ∅ : Assignment L R
  _and_↦_ : Assignment L R → L → R → Assignment L R

-- helper function for a nicer beginning of list
assign_↦_ : {L R : Set} → L → R → Assignment L R
assign l ↦ r = ∅ and l ↦ r

infix 4 _∋_↦_
data _∋_↦_ : {L R : Set} → Assignment L R → L → R → Set where
   here : ∀ {L R : Set} {l : L} {r : R} {A}
       ---------------------
     → A and l ↦ r ∋ l ↦ r

   there : ∀ {L R : Set} {l l' : L} {r r' : R} {A}
     → l ≢ l'
     → A ∋ l ↦ r
       ---------------------
     → A and l' ↦ r' ∋ l ↦ r

-- Smart constructor for there that will make Agda
-- figure out the proof. This is still magic to me.
there' : ∀ {R : Set} {l l' : Dimension} {r r' : R} {A}
  → {l≢l' : False (l ≟ l')}
  → A ∋ l ↦ r
    ---------------------
  → A and l' ↦ r' ∋ l ↦ r
there' {l≢l' = l≢l'} = there (toWitnessFalse l≢l')

Configuration : Set
Configuration = Assignment Dimension Tag₂
```

Denotational semantics of binary choice calculus as big-step semantics:
```agda
infix 4 _⊢_⟶_
data _⊢_⟶_ : ∀ {i A} → Configuration → CC₂ i A → Variant A → Set where
  ξ-A₂ : ∀ {A c j a} {es : List (CC₂ j A)}
    → (esᵥ : All (λ e → ∃[ v ] (c ⊢ e ⟶ v)) es)
      -------------------------------------------------------
    → c ⊢ (Artifact₂ a es) ⟶ (Artifactᵥ a (reduce proj₁ esᵥ))

  C-l : ∀ {A c j D} {l r : CC₂ j A} {v : Variant A}
    → c ∋ D ↦ left -- formulate this as evidence predicate ⊤?
    → c ⊢ l ⟶ v
      --------------------
    → c ⊢ D ⟨ l , r ⟩₂ ⟶ v

  C-r : ∀ {A c j D} {l r : CC₂ j A} {v : Variant A}
    → c ∋ D ↦ right
    → c ⊢ r ⟶ v
      --------------------
    → c ⊢ D ⟨ l , r ⟩₂ ⟶ v

ξ-leaf : ∀ {A : Set} {c} {a : A}
    ------------------------------------
  → c ⊢ Artifact₂ a [] ⟶ Artifactᵥ a []
ξ-leaf = ξ-A₂ []
```

Example:
```
leaf : ∀ {i A} → A → CC₂ (↑ i) A
leaf a = Artifact₂ a []

leafᵥ : ∀ {A} → A → Variant A
leafᵥ a = Artifactᵥ a []
```

Example 1:
```
bin : ∀ {i} → CC₂ (↑ ↑ i) String
bin = "D" ⟨ leaf "l" , leaf "r" ⟩₂

_ : (assign "D" ↦ left) ⊢ bin ⟶ leafᵥ "l"
_ = C-l here ξ-leaf
```

Example 2:
```agda
burger : ∀ {i} → CC₂ (↑ ↑ ↑ i) String
burger = Artifact₂ "Sandwich" (
      leaf "Salad"
    ∷ "Sauce" ⟨ leaf "Ketchup" , leaf "Mayonnaise" ⟩₂
    ∷ "Patty" ⟨ leaf "Soy" , leaf "Halloumi" ⟩₂
    ∷ [])

burger-stabil : Variant String
burger-stabil = Artifactᵥ "Sandwich" (
    leafᵥ "Salad"
  ∷ leafᵥ "Ketchup"
  ∷ leafᵥ "Halloumi"
  ∷ [])

burger-stabil-conf : Configuration
burger-stabil-conf = assign "Sauce" ↦ left and "Patty" ↦ right

_ : burger-stabil-conf ⊢ burger ⟶ burger-stabil
_ = ξ-A₂ (
    ((leafᵥ "Salad") , ξ-leaf)
  ∷ ((leafᵥ "Ketchup") , C-l (there' here) ξ-leaf)
  ∷ ((leafᵥ "Halloumi") , C-r here ξ-leaf)
  ∷ []
  )
```
