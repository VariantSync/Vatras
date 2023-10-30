{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Translation.Lang.2ADT-to-NADT {F : 𝔽} {A : 𝔸} where

open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Size using (∞; ↑_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

import Data.IndexedSet

import Framework.V2.Constructs.Choices
open Framework.V2.Constructs.Choices.Choiceₙ renaming (map to mapₙ)

open import Framework.V2.Variants using (VariantSetoid; GrulerVariant)
open import Framework.V2.Lang.2ADT
open import Framework.V2.Lang.NADT

import Framework.V2.Translation.Construct.2Choice-to-NChoice {0ℓ} {F} as 2→N
open 2→N.Translate using (convert)

compile : ∀ {i} → 2ADT F i A → NADT F i A
compile (2ADTAsset a)      = NADTAsset a
compile (2ADTChoice {i} c) = NADTChoice (mapₙ compile (convert (Eq.setoid (2ADT F i A)) c))

module Preservation where
  -- open Data.IndexedSet (VariantSetoid GrulerVariant A) using () renaming (_≅_ to _≋_)

  -- TODO: Prove Preservation of compile
  -- open 2→N.Translate.Preservation 2ADTVL NADTVL compile conf' fnoc' using (preserves-conf; preserves-fnoc)

  -- preserves-l : ∀ (e : 2ADT A) → Conf-Preserves 2ADTVL NADTVL e (compile e) conf'
  -- preserves-l (2ADTAsset _) _ = refl
  -- preserves-l (2ADTChoice (D ⟨ l , r ⟩)) c =
  --   begin
  --     ⟦ 2ADTChoice (D ⟨ l , r ⟩) ⟧-2adt c
  --   ≡⟨⟩
  --     BinaryChoice-Semantics 2ADTVL (D ⟨ l , r ⟩) c
  --   ≡⟨ preserves-conf D l r (default-conf-satisfies-spec D) (preserves-l l) (preserves-l r) c ⟩
  --     Choice-Semantics NADTVL (convert (D ⟨ l , r ⟩)) (conf' c)
  --   ≡⟨⟩
  --     ⟦ compile (2ADTChoice (D ⟨ l , r ⟩)) ⟧-nadt (conf' c)
  --   ∎

  -- preserves-r : ∀ (e : 2ADT A) → Fnoc-Preserves 2ADTVL NADTVL e (compile e) fnoc'
  -- preserves-r (2ADTAsset _) _ = refl
  -- preserves-r (2ADTChoice (D ⟨ l , r ⟩)) c = preserves-fnoc D l r (default-fnoc-satisfies-spec D) (preserves-r l) (preserves-r r) c

  -- preserves : ∀ (e : 2ADT A) → ⟦ e ⟧-2adt ≋ ⟦ compile e ⟧-nadt
  -- preserves e = ⊆-by-index-translation conf' (preserves-l e)
  --           and ⊆-by-index-translation fnoc' (preserves-r e)
