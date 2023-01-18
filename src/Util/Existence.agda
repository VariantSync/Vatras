{-# OPTIONS --sized-types #-}

module Util.Existence where

open import Agda.Primitive using (Level; _⊔_)
open import Data.Product using (Σ)
open import Size using (SizeUniv)

-- Existence of sizes

record Σ-Size {l : Level} (i : SizeUniv) (B : i → Set l) : Set l where
  constructor _,_
  field
    fst : i
    snd : B fst
open Σ-Size public

∃-Size : ∀ {l : Level} {A : SizeUniv} → (A → Set l) → Set l
∃-Size = Σ-Size _

syntax ∃-Size (λ i → B) = ∃-Size[ i ] B

-- Existence syntax that also explicitly lists the type of the existing value

∃-syntax-with-type : ∀ {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
∃-syntax-with-type = Σ

syntax ∃-syntax-with-type A (λ x → B) = ∃[ x ∈ A ] B