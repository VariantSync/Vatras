{-# OPTIONS --allow-unsolved-metas #-}
module Translation.Construct.2Choice-to-Choice {Q : Set} where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using () renaming (_,_ to _and_)
open import Level using (0ℓ)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

open import Framework.Definitions using (𝔽)
open import Framework.Compiler using (ConstructCompiler)
open import Construct.Choices

open 2Choice using (_⟨_,_⟩)
open Choice using (_⟨_⟩)

{-|
ConfContract and FnocContract define the requirements we have on translated configurations
to prove preservation of the conversion from binary to n-ary choices.

The requirement for translating binary to n-ary configurations is
that there exist two natural numbers that we can associate with the boolean values true and false.
To simplify things, we fix these two numbers to be 0 for true, and 1 for false. These values are chosen such that
`D < l ,  r       >` lines up with
`D < l :: r :: [] >`
-}
record ConfContract (f : Q) (conf : 2Choice.Config Q → Choice.Config Q) : Set where
  field
    false→1 : ∀ (c : 2Choice.Config Q)
      → c f ≡ false
      → (conf c) f ≡ 1

    true→0 : ∀ (c : 2Choice.Config Q)
      → c f ≡ true
      → (conf c) f ≡ 0
open ConfContract

{-|
ConfContract and FnocContract define the requirements we have on translated configurations
to prove preservation of the conversion from binary to n-ary choices.

The requirement for translating n-ary to binary configurations is
that we can associate each natural numbers with the boolean values true and false,
such that the association is inverse to ConfContract.
Hence, we associate 0 with true and all other numbers with false.
-}
record FnocContract (f : Q) (fnoc : Choice.Config Q → 2Choice.Config Q) : Set where
  field
    suc→false : ∀ {n} (c : Choice.Config Q)
      → c f ≡ suc n
      → (fnoc c) f ≡ false

    zero→true : ∀ (c : Choice.Config Q)
      → c f ≡ zero
      → (fnoc c) f ≡ true
open FnocContract

default-conf : 2Choice.Config Q → Choice.Config Q
default-conf cb f with cb f
... | false = 1
... | true  = 0

default-fnoc : Choice.Config Q → 2Choice.Config Q
default-fnoc cn f with cn f
... | zero    = true
... | (suc _) = false

default-conf-satisfies-contract : ∀ (f : Q) → ConfContract f default-conf
false→1 (default-conf-satisfies-contract f) c cf≡false rewrite cf≡false = refl
true→0  (default-conf-satisfies-contract f) c cf≡true  rewrite cf≡true  = refl

default-fnoc-satisfies-contract : ∀ (f : Q) → FnocContract f default-fnoc
suc→false (default-fnoc-satisfies-contract f) c cf≡suc  rewrite cf≡suc  = refl
zero→true (default-fnoc-satisfies-contract f) c cf≡zero rewrite cf≡zero = refl

module Translate {ℓ} (S : Setoid ℓ ℓ) where
  open Setoid S
  module ≈-Eq = IsEquivalence isEquivalence

  -- TODO: This should be put into a ConstructCompiler.
  --       However, that might not be possible because it would require to abstract
  --       arbitrary requirements on the configuration compiler.
  --       Maybe this could be done via type parameters but lets see whether it pays off.
  convert : 2Choice.Syntax Q Carrier → Choice.Syntax Q Carrier
  convert (D ⟨ l , r ⟩) = D ⟨ l ∷ r ∷ [] ⟩

  module Preservation
    (conf : 2Choice.Config Q → Choice.Config Q)
    (fnoc : Choice.Config Q → 2Choice.Config Q)
    (chc : 2Choice.Syntax Q Carrier)
    where
    open Data.IndexedSet S using (_⊆[_]_; _≅[_][_]_; _≅_)

    preserves-conf :
        ConfContract (2Choice.Syntax.dim chc) conf
      → 2Choice.⟦ chc ⟧ ⊆[ conf ] Choice.⟦ convert chc ⟧
    preserves-conf conv c with c (2Choice.Syntax.dim chc) in eq
    ... | false rewrite false→1 conv c eq = ≈-Eq.refl
    ... | true  rewrite true→0  conv c eq = ≈-Eq.refl

    preserves-fnoc :
        FnocContract (2Choice.Syntax.dim chc) fnoc
      → Choice.⟦ convert chc ⟧ ⊆[ fnoc ] 2Choice.⟦ chc ⟧
    preserves-fnoc vnoc c with c (2Choice.Syntax.dim chc) in eq
    ... | zero  rewrite zero→true vnoc c eq = ≈-Eq.refl
    ... | suc _ rewrite suc→false vnoc c eq = ≈-Eq.refl

    convert-preserves :
        ConfContract (2Choice.Syntax.dim chc) conf
      → FnocContract (2Choice.Syntax.dim chc) fnoc
      → 2Choice.⟦ chc ⟧ ≅[ conf ][ fnoc ] Choice.⟦ convert chc ⟧
    convert-preserves conv vnoc = preserves-conf conv and preserves-fnoc vnoc

  -- compiler : ∀ (F : 𝔽) → ConstructCompiler (C₂ F) (Cₙ F)
  -- compiler F = record
  --   { compile = {!convert!}
  --   ; config-compiler = {!!}
  --   ; stable = {!!}
  --   ; preserves = {!!}
  --   }
