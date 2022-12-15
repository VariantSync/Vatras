# Alternative Formulation of Semantics as Transition Relations (Currently Playground)

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module BigStep where
```

## Imports
```agda
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Size using (Size; ↑_; ∞)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≗_; refl)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Imports of own modules
open import CC using (CC₂; Artifact₂; _⟨_,_⟩₂; Configuration₂; left; right)
open import SemanticDomains using (Variant; Artifactᵥ)
open import Extensionality
  using (extensionality)

open import Data.List.Relation.Unary.All using (All; reduce; []; _∷_)
```

## Binary Choice Calculus

```agda
-- Denotational Semantics as big-step relation

infix 4 _⊢_⟶_
data _⊢_⟶_ : ∀ {i A} → Configuration₂ → CC₂ i A → Variant A → Set where
  ξ-A₂ : ∀ {A c j a} {es : List (CC₂ j A)}
    → (esᵥ : All (λ e → ∃[ v ] (c ⊢ e ⟶ v)) es)
      -------------------------------------------------------
    → c ⊢ (Artifact₂ a es) ⟶ (Artifactᵥ a (reduce proj₁ esᵥ))

  C-l : ∀ {A c j D} {l r : CC₂ j A} {v : Variant A}
    → c D ≡ left -- formulate this as evidence predicate ⊤?
    → c ⊢ l ⟶ v
      --------------------
    → c ⊢ D ⟨ l , r ⟩₂ ⟶ v

  C-r : ∀ {A c j D} {l r : CC₂ j A} {v : Variant A}
    → c D ≡ right
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

_ : (λ _ → left) ⊢ bin ⟶ leafᵥ "l"
_ = C-l refl ξ-leaf
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

burger-stabil-conf : Configuration₂
burger-stabil-conf "Sauce" = left
burger-stabil-conf "Patty" = right
burger-stabil-conf _ = left

_ : burger-stabil-conf ⊢ burger ⟶ burger-stabil
_ = ξ-A₂ (
    ((leafᵥ "Salad") , ξ-leaf)
  ∷ ((leafᵥ "Ketchup") , C-l refl ξ-leaf)
  ∷ ((leafᵥ "Halloumi") , C-r refl ξ-leaf)
  ∷ []
  )
```
