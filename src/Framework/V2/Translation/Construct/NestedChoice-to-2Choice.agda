{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.Construct.NestedChoice-to-2Choice where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
import Relation.Binary.PropositionalEquality as Eq

open import Function.Base using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.Annotation.IndexedName using (IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩)
open Chc.VLChoice₂ using () renaming (Syntax to 2Choice; Semantics to 2Choice-sem; Construct to ChoiceConstructor)
open import Framework.V2.Translation.Construct.NChoice-to-2Choice

module Embed
  {V : 𝕍} {F : 𝔽} {A : 𝔸}
  (Γ : VariabilityLanguage V (IndexedName F) Bool)
  (constr : (ChoiceConstructor V (IndexedName F)) ⟦∈⟧ Γ)
  where

  open Translate {F} (Eq.setoid (Expression Γ A))
  open Setoid (Eq.setoid (V A)) using (_≈_)

  embed : ∀ {i} → NestedChoice i → Expression Γ A
  embed (val v) = v
  embed (nchc c) = cons (make constr) (map (embed) c)
    where
    open Chc.Choice₂ using (map)

  embed-preserves : ∀ {i}
    → (e : NestedChoice i)
    → (c : Config (IndexedName F) Bool)
    → (valid : at-least-true-once c)
    ---------------------------------------------------------------
    → Semantics Γ (embed e) c ≈ Semantics Γ (⟦ e ⟧ (c and valid)) c
  embed-preserves e c valid = induction e
    where
    induction : ∀ {i}
      → (e : NestedChoice i)
      → Semantics Γ (embed e) c ≈ Semantics Γ (⟦ e ⟧ (c and valid)) c
    induction (val v) = refl
    induction (nchc (dim ⟨ l , r ⟩))
      rewrite preservation constr (dim ⟨ embed l , embed r ⟩) c
      with c dim
    ... | true = induction l
    ... | false = induction r
