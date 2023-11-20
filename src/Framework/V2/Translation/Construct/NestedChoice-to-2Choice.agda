{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.Construct.NestedChoice-to-2Choice (Q : Set) where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; proj₁; Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

open import Function.Base using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.Annotation.IndexedName using (IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choiceₙ using () renaming (Config to Configₙ)
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂)
open Chc.VLChoice₂ (IndexedName Q) using () renaming (Syntax to Choice₂; Semantics to Choice₂-sem; Construct to Choice₂-Constructor)

import Framework.V2.Translation.Construct.NChoice-to-2Choice as NChoice-to-2Choice
open NChoice-to-2Choice using (NestedChoice; value; choice; evalConfig)
open NChoice-to-2Choice {Q} using (2Config)

2Choice-sem : ∀ (V : 𝕍) → ℂ-Semantics V 2Config Choice₂
2Choice-sem V fnoc Γ cons conf = Choice₂-sem V (proj₁ ∘ fnoc) Γ cons conf

ChoiceConstructor : ∀ (V : 𝕍) → VariabilityConstruct V 2Config
ChoiceConstructor V = con Choice₂ with-sem 2Choice-sem V

module Embed
  {V : 𝕍} {A : 𝔸}
  (Γ : VariabilityLanguage V 2Config)
  (constr : ChoiceConstructor V ⟦∈⟧ Γ)
  where

  open NChoice-to-2Choice.Translate {Q} (Eq.setoid (Expression Γ A))
  open Data.IndexedSet (Eq.setoid (V A)) using (_≅_; ≗→≅)


  embed : ∀ {i} → NestedChoice i (Expression Γ A) → Expression Γ A
  embed (value v) = v
  embed (choice c) = cons (make constr) (map embed c)
    where
    open Chc.Choice₂ using (map)

  embed-preserves : ∀ {i}
    → (e : NestedChoice i (Expression Γ A))
    → Semantics Γ (embed e) ≅ λ c → Semantics Γ (⟦ e ⟧ c) c
  embed-preserves e = ≗→≅ (induction e)
    where
    induction : ∀ {i}
      → (e : NestedChoice i (Expression Γ A))
      → Semantics Γ (embed e) ≗ λ c → Semantics Γ (⟦ e ⟧ c) c
    induction (value v) c = refl
    induction (choice (dim ⟨ l , r ⟩)) c
      rewrite preservation constr (dim ⟨ embed l , embed r ⟩) c
      with evalConfig c dim
    ... | true = induction l c
    ... | false = induction r c
