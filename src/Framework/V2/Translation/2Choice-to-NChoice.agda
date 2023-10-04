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
open Chc.Choice₂ Q using () renaming (Config to Config₂)
open Chc.Choiceₙ Q using () renaming (Config to Configₙ)

{-|
ConfSpec and FnocSpec define the requirements we have on translated configurations
to prove preservation of the conversion from binary to n-ary choices.
-}
record ConfSpec (f : Q) (conf : Config₂ → Configₙ) : Set ℓ₁ where
  field
    false→1 : ∀ (c : Config₂)
      → c f ≡ false
      → (conf c) f ≡ 1

    true→0 : ∀ (c : Config₂)
      → c f ≡ true
      → (conf c) f ≡ 0
open ConfSpec

record FnocSpec (f : Q) (fnoc : Configₙ → Config₂) : Set ℓ₁ where
  field
    suc→false : ∀ {n} (c : Configₙ)
      → c f ≡ suc n
      → (fnoc c) f ≡ false

    zero→true : ∀ (c : Configₙ)
      → c f ≡ zero
      → (fnoc c) f ≡ true
open FnocSpec

default-conf : Config₂ → Configₙ
(default-conf cb) f with cb f
... | false = 1
... | true  = 0

default-fnoc : Configₙ → Config₂
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

  open Chc.Choice₂ Q
    using (_⟨_,_⟩)
    renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂)
  open Chc.Choiceₙ Q
    using (_⟨_⟩)
    renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ)

  convert : 2Choice Carrier → NChoice Carrier
  convert (D ⟨ l , r ⟩) = D ⟨ l ∷ r ∷ [] ⟩

  module Preservation
    (conf : Config₂ → Configₙ)
    (fnoc : Configₙ → Config₂)
    (D : Q)
    (l r : Carrier)
    where
    open Data.IndexedSet S using (⊆-by-index-translation) renaming (_≅_ to _≋_)

    preserves-conf :
        ConfSpec D conf
      → (c : Config₂)
      →   (⟦ D ⟨ l , r ⟩ ⟧₂ c)
        ≈ (⟦ convert (D ⟨ l , r ⟩) ⟧ₙ (conf c))
    preserves-conf conv c with c D in eq
    ... | false rewrite false→1 conv c eq = ≈-Eq.refl
    ... | true  rewrite true→0  conv c eq = ≈-Eq.refl

    preserves-fnoc :
        FnocSpec D fnoc
      → (c : Configₙ)
      →   ⟦ convert (D ⟨ l , r ⟩) ⟧ₙ c
        ≈ ⟦ D ⟨ l , r ⟩ ⟧₂ (fnoc c)
    preserves-fnoc vnoc c with c D in eq
    ... | zero  rewrite zero→true vnoc c eq = ≈-Eq.refl
    ... | suc _ rewrite suc→false vnoc c eq = ≈-Eq.refl

    convert-preserves :
      ∀ (conv : ConfSpec D conf)
      → (vnoc : FnocSpec D fnoc)
      →   ⟦ D ⟨ l , r ⟩ ⟧₂
        ≋ ⟦ convert (D ⟨ l , r ⟩) ⟧ₙ
    convert-preserves conv vnoc =
          ⊆-by-index-translation conf (preserves-conf conv)
      and ⊆-by-index-translation fnoc (preserves-fnoc vnoc)
