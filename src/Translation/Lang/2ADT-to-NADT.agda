{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Translation.Lang.2ADT-to-NADT {F : 𝔽} {A : 𝔸} where

open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Size using (∞; ↑_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

import Data.IndexedSet

open import Construct.Choices
open import Construct.NestedChoice using (value; choice)

open import Framework.Variants using (GrulerVariant)
open import Lang.2ADT
open import Lang.NADT

import Translation.Construct.2Choice-to-Choice {F} as 2Choice-to-Choice
open 2Choice-to-Choice.Translate using (convert)

compile : ∀ {i} → 2ADT F i A → NADT F i A
compile (value a)      = NADTAsset a
compile (choice {i} c) = NADTChoice (Choice.map compile (convert (Eq.setoid (2ADT F i A)) c))

module Preservation where
  -- open Data.IndexedSet (VariantSetoid GrulerVariant A) using () renaming (_≅_ to _≋_)

  -- TODO: Prove Preservation of compile
  -- open 2Choice-to-Choice.Translate.Preservation 2ADTVL NADTVL compile conf' fnoc' using (preserves-conf; preserves-fnoc)

  -- preserves-l : ∀ (e : 2ADT A) → Conf-Preserves 2ADTVL NADTVL e (compile e) conf'
  -- preserves-l (value _) _ = refl
  -- preserves-l (choice (D ⟨ l , r ⟩)) c =
  --   begin
  --     ⟦ choice (D ⟨ l , r ⟩) ⟧-2adt c
  --   ≡⟨⟩
  --     BinaryChoice-Semantics 2ADTVL (D ⟨ l , r ⟩) c
  --   ≡⟨ preserves-conf D l r (default-conf-satisfies-spec D) (preserves-l l) (preserves-l r) c ⟩
  --     Choice-Semantics NADTVL (convert (D ⟨ l , r ⟩)) (conf' c)
  --   ≡⟨⟩
  --     ⟦ compile (choice (D ⟨ l , r ⟩)) ⟧-nadt (conf' c)
  --   ∎

  -- preserves-r : ∀ (e : 2ADT A) → Fnoc-Preserves 2ADTVL NADTVL e (compile e) fnoc'
  -- preserves-r (value _) _ = refl
  -- preserves-r (choice (D ⟨ l , r ⟩)) c = preserves-fnoc D l r (default-fnoc-satisfies-spec D) (preserves-r l) (preserves-r r) c

  -- preserves : ∀ (e : 2ADT A) → ⟦ e ⟧-2adt ≋ ⟦ compile e ⟧-nadt
  -- preserves e = ⊆-by-index-translation conf' (preserves-l e)
  --           and ⊆-by-index-translation fnoc' (preserves-r e)
