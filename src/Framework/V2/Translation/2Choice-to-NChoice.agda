{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.2Choice-to-NChoice {ℓ₁} {Q : Set ℓ₁} where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using () renaming (_,_ to _and_)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Data.IndexedSet

open import Framework.V2.Definitions using (𝔽)
open import Framework.V2.Compiler using (ConstructCompiler)
open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)
open Chc.VLChoice₂ using () renaming (Construct to C₂)
open Chc.VLChoiceₙ using () renaming (Construct to Cₙ)

{-|
ConfContract and FnocContract define the requirements we have on translated configurations
to prove preservation of the conversion from binary to n-ary choices.

The requirement for translating binary to n-ary configurations is
that there exist two natural numbers that we can associate with the boolean values true and false.
To simplify things, we fix these two numbers to be 0 for true, and 1 for false.
-}
record ConfContract (f : Q) (conf : Config₂ Q → Configₙ Q) : Set ℓ₁ where
  field
    false→1 : ∀ (c : Config₂ Q)
      → c f ≡ false
      → (conf c) f ≡ 1

    true→0 : ∀ (c : Config₂ Q)
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
record FnocContract (f : Q) (fnoc : Configₙ Q → Config₂ Q) : Set ℓ₁ where
  field
    suc→false : ∀ {n} (c : Configₙ Q)
      → c f ≡ suc n
      → (fnoc c) f ≡ false

    zero→true : ∀ (c : Configₙ Q)
      → c f ≡ zero
      → (fnoc c) f ≡ true
open FnocContract

default-conf : Config₂ Q → Configₙ Q
default-conf cb f with cb f
... | false = 1
... | true  = 0

default-fnoc : Configₙ Q → Config₂ Q
default-fnoc cn f with cn f
... | zero    = true
... | (suc _) = false

default-conf-satisfies-contract : ∀ (f : Q) → ConfContract f default-conf
false→1 (default-conf-satisfies-contract f) c cf≡false rewrite cf≡false = refl
true→0  (default-conf-satisfies-contract f) c cf≡true  rewrite cf≡true  = refl

default-fnoc-satisfies-contract : ∀ (f : Q) → FnocContract f default-fnoc
suc→false (default-fnoc-satisfies-contract f) c cf≡suc  rewrite cf≡suc  = refl
zero→true (default-fnoc-satisfies-contract f) c cf≡zero rewrite cf≡zero = refl

module Translate {ℓ₂} (S : Setoid ℓ₁ ℓ₂) where
  open Setoid S
  module ≈-Eq = IsEquivalence isEquivalence

  -- TODO: This should be put into a ConstructCompiler.
  --       However, that might not be possible because it would require to abstract
  --       arbitrary requirements on the configuration compiler.
  --       Maybe this could be done via type parameters but lets see whether it pays off.
  convert : 2Choice Q Carrier → NChoice Q Carrier
  convert (D ⟨ l , r ⟩) = D ⟨ l ∷ r ∷ [] ⟩

  module Preservation
    (conf : Config₂ Q → Configₙ Q)
    (fnoc : Configₙ Q → Config₂ Q)
    (chc : 2Choice Q Carrier)
    where
    open Data.IndexedSet S using (_⊆[_]_; _≅[_][_]_; _≅_)

    preserves-conf :
        ConfContract (2Choice.dim chc) conf
      → ⟦ chc ⟧₂ ⊆[ conf ] ⟦ convert chc ⟧ₙ
    preserves-conf conv c with c (2Choice.dim chc) in eq
    ... | false rewrite false→1 conv c eq = ≈-Eq.refl
    ... | true  rewrite true→0  conv c eq = ≈-Eq.refl

    preserves-fnoc :
        FnocContract (2Choice.dim chc) fnoc
      → ⟦ convert chc ⟧ₙ ⊆[ fnoc ] ⟦ chc ⟧₂
    preserves-fnoc vnoc c with c (2Choice.dim chc) in eq
    ... | zero  rewrite zero→true vnoc c eq = ≈-Eq.refl
    ... | suc _ rewrite suc→false vnoc c eq = ≈-Eq.refl

    convert-preserves :
        ConfContract (2Choice.dim chc) conf
      → FnocContract (2Choice.dim chc) fnoc
      → ⟦ chc ⟧₂ ≅[ conf ][ fnoc ] ⟦ convert chc ⟧ₙ
    convert-preserves conv vnoc = preserves-conf conv and preserves-fnoc vnoc

  -- compiler : ∀ (F : 𝔽) → ConstructCompiler (C₂ F) (Cₙ F)
  -- compiler F = record
  --   { compile = {!convert!}
  --   ; config-compiler = {!!}
  --   ; stable = {!!}
  --   ; preserves = {!!}
  --   }
