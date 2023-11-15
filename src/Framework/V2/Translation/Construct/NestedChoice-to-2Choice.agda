{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.Construct.NestedChoice-to-2Choice where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

open import Function.Base using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.Annotation.IndexedName using (IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Standard-Semantics to ⟦_⟧₂)
open Chc.VLChoice₂ using () renaming (Syntax to 2Choice)
open import Framework.V2.Translation.Construct.NChoice-to-2Choice

module Embed
  {V : 𝕍} {F : 𝔽} {A : 𝔸}
  (Γ : VariabilityLanguage V (IndexedName F) Bool)
  (constr : IndexedName F ⊢ 2Choice ∈ₛ Expression Γ)
  where

  open Translate {F} (Eq.setoid (Expression Γ A))
  open Data.IndexedSet (Eq.setoid (V A)) using (_≐_; _≅_; ≐→≅)

  embed : ∀ {i} → NestedChoice i → Expression Γ A
  embed (val v) = v
  embed (nchc c) = cons constr (map (embed) c)
    where
    open Chc.Choice₂ using (map)

  embed-preserves : ∀ {i}
    → (config-is-valid : (c : Config (IndexedName F) Bool) → at-least-true-once c)
    → (∀ e → Semantics Γ (cons constr e) ≡ λ c → Semantics Γ (⟦ e ⟧₂ c) c)
    → (e : NestedChoice i)
    -------------------------------------------------------------------------------
    → Semantics Γ (embed e) ≅ λ c → Semantics Γ (⟦ e ⟧ (c and config-is-valid c)) c
  embed-preserves config-is-valid constr-semantic e = ≐→≅ (induction e)
    where
    induction : ∀ {i}
      → (e : NestedChoice i)
      → Semantics Γ (embed e) ≐ λ c → Semantics Γ (⟦ e ⟧ (c and config-is-valid c)) c
    induction (val v) c = refl
    induction (nchc (dim ⟨ l , r ⟩)) c
      rewrite constr-semantic (dim ⟨ embed l , embed r ⟩)
      with c dim
    ... | true = induction l c
    ... | false = induction r c
