{-# OPTIONS --sized-types #-}

module Construct.GrulerArtifacts where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Definitions
open import Framework.Variants
open import Framework.VariabilityLanguage
open import Framework.Construct

-- this is just a value
data Leaf {ℓ} (A : Set ℓ) : Set ℓ where
  leaf : (a : A) → Leaf A

-- this is just a pair
record ParallelComposition {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _∥_
  field
    l : A
    r : A

module VLLeaf where
  Syntax : ℂ
  Syntax _ A = Leaf A

  make-leaf :
    ∀ {E : 𝔼} → Syntax ∈ₛ E
    → {A : 𝔸} → A
    → E A
  make-leaf mkLeaf a = cons mkLeaf (leaf a)

  elim-leaf : ∀ {V} → Syntax ∈ₛ V → ∀ {A} → Leaf A → V A
  elim-leaf leaf∈V l = cons leaf∈V l

  Construct : PlainConstruct
  PSyntax Construct = Syntax
  pcong Construct _ e _ = e

  Leaf∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons Leaf∈ₛGrulerVariant (leaf a) = asset a
  snoc Leaf∈ₛGrulerVariant (asset a) = just (leaf a)
  snoc Leaf∈ₛGrulerVariant (_ ∥ _) = nothing
  id-l Leaf∈ₛGrulerVariant (leaf _) = refl

module VLParallelComposition where
  Syntax : ℂ
  Syntax E A = ParallelComposition (E A)

  Construct : PlainConstruct
  PSyntax Construct = Syntax
  pcong Construct ⟪ _ , _ , ⟦_⟧ ⟫ (l ∥ r) c = ⟦ l ⟧ c ∥ ⟦ r ⟧ c

  ParallelComposition∈ₛGrulerVariant : Syntax ∈ₛ GrulerVariant
  cons ParallelComposition∈ₛGrulerVariant (l ∥ r) = l ∥ r
  snoc ParallelComposition∈ₛGrulerVariant (asset a) = nothing
  snoc ParallelComposition∈ₛGrulerVariant (l ∥ r) = just (l ∥ r)
  id-l ParallelComposition∈ₛGrulerVariant (l ∥ r) = refl
