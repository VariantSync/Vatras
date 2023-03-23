{-# OPTIONS --sized-types #-}

module VariantIsomorphismPlayground where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)

open import Data.List using (List)
open import Data.List.NonEmpty

open import Function
open import Size
open import Util.SizeJuggle

Arity : Set₁
Arity = Set → Set

one : Arity
one A = A

at-least-one : Arity
at-least-one A = List⁺ A

any : Arity
any A = List A

GrammarRule : (V : Set) (A : Arity) → Set
GrammarRule V A = V

Grammar : Set₁
Grammar = Set → Set

arity-of : ∀ {V : Set} {A : Arity} → GrammarRule V A → Arity
arity-of {A = A} _ = A

data Skeleton (G : Grammar) : Set where
  bone : ∀ {A : Set}
    → (g : G A)
    → arity-of g (Skeleton G)
    → Skeleton G

record ObjectLanguage (A : Set) (L : Set) : Set where
  field
    embed   : A → Skeleton L
    restore : Skeleton L → A
    iso-l   : embed ∘ restore ≗ id
    iso-r   : restore ∘ embed ≗ id

-- example
open import Lang.Annotation.Name
open import Lang.CCC using ()

-- data CCCGrammar (A : Set) : Set where

-- ArtifactLabel : GrammarRule A any → CCCGrammar A
  -- ChoiceLabel   : GrammarRule Dimension at-least-one → CCCGrammar A

