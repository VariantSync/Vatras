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

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Config to Configₙ)

{-|
ConfSpec and FnocSpec define the requirements we have on translated configurations
to prove preservation of the conversion from binary to n-ary choices.
-}
record ConfSpec (f : Q) (conf : Config₂ Q → Configₙ Q) : Set ℓ₁ where
  field
    false→1 : ∀ (c : Config₂ Q)
      → c f ≡ false
      → (conf c) f ≡ 1

    true→0 : ∀ (c : Config₂ Q)
      → c f ≡ true
      → (conf c) f ≡ 0
open ConfSpec

record FnocSpec (f : Q) (fnoc : Configₙ Q → Config₂ Q) : Set ℓ₁ where
  field
    suc→false : ∀ {n} (c : Configₙ Q)
      → c f ≡ suc n
      → (fnoc c) f ≡ false

    zero→true : ∀ (c : Configₙ Q)
      → c f ≡ zero
      → (fnoc c) f ≡ true
open FnocSpec

default-conf : Config₂ Q → Configₙ Q
(default-conf cb) f with cb f
... | false = 1
... | true  = 0

default-fnoc : Configₙ Q → Config₂ Q
(default-fnoc cn) f with cn f
... | zero    = true
... | (suc _) = false

default-conf-satisfies-spec : ∀ (f : Q) → ConfSpec f default-conf
false→1 (default-conf-satisfies-spec f) c cf≡false rewrite cf≡false = refl
true→0  (default-conf-satisfies-spec f) c cf≡true  rewrite cf≡true  = refl

default-fnoc-satisfies-spec : ∀ (f : Q) → FnocSpec f default-fnoc
suc→false (default-fnoc-satisfies-spec f) c cf≡suc  rewrite cf≡suc  = refl
zero→true (default-fnoc-satisfies-spec f) c cf≡zero rewrite cf≡zero = refl

module Translate {ℓ₂} (S : Setoid ℓ₁ ℓ₂) where
  open Setoid S
  module ≈-Eq = IsEquivalence isEquivalence

  open Chc.Choice₂ renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂)
  open Chc.Choiceₙ renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ)

  -- TODO: Can we abstract this as some sort of "external" compiler with custom syntax and semantics, which can be composed with ConstructCompilers?
  convert : 2Choice Q Carrier → NChoice Q Carrier
  convert (D ⟨ l , r ⟩) = D ⟨ l ∷ r ∷ [] ⟩

  module Preservation
    (conf : Config₂ Q → Configₙ Q)
    (fnoc : Configₙ Q → Config₂ Q)
    (D : Q)
    (l r : Carrier)
    where
    open Data.IndexedSet S using (_⊆[_]_; _≅[_][_]_; _≅_)

    preserves-conf :
        ConfSpec D conf
      → ⟦ D ⟨ l , r ⟩ ⟧₂ ⊆[ conf ] ⟦ convert (D ⟨ l , r ⟩) ⟧ₙ
    preserves-conf conv c with c D in eq
    ... | false rewrite false→1 conv c eq = ≈-Eq.refl
    ... | true  rewrite true→0  conv c eq = ≈-Eq.refl

    preserves-fnoc :
        FnocSpec D fnoc
      → ⟦ convert (D ⟨ l , r ⟩) ⟧ₙ ⊆[ fnoc ] ⟦ D ⟨ l , r ⟩ ⟧₂
    preserves-fnoc vnoc c with c D in eq
    ... | zero  rewrite zero→true vnoc c eq = ≈-Eq.refl
    ... | suc _ rewrite suc→false vnoc c eq = ≈-Eq.refl

    -- TODO: This theorem requires D, l, and r to be known but we can use any choice in fact.
    --       => Generalize.
    convert-preserves :
        ConfSpec D conf
      → FnocSpec D fnoc
      → ⟦ D ⟨ l , r ⟩ ⟧₂ ≅[ conf ][ fnoc ] ⟦ convert (D ⟨ l , r ⟩) ⟧ₙ
    convert-preserves conv vnoc = preserves-conf conv and preserves-fnoc vnoc
