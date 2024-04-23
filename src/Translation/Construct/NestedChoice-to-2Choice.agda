{-# OPTIONS --allow-unsolved-metas #-}
module Translation.Construct.NestedChoice-to-2Choice where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; proj₁; Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

open import Function.Base using (id; _∘_)

open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Framework.Annotation.IndexedName using (IndexedName)
open import Construct.Choices
open 2Choice using (_⟨_,_⟩)

import Translation.Construct.Choice-to-2Choice as Choice-to-2Choice
open Choice-to-2Choice using (NestedChoice; value; choice; evalConfig)
module Choice-to-2Choice-explicit Q = Choice-to-2Choice {Q}
open Choice-to-2Choice-explicit using (2Config)

2Choice : 𝔽 → ℂ
2Choice F E A = VL2Choice.Syntax (IndexedName F) E A

2Choice-sem : ∀ (F : 𝔽) → VariationalConstruct-Semantics (2Config F) (2Choice F)
2Choice-sem F Γ fnoc cons conf = VL2Choice.Semantics (IndexedName F) Γ (proj₁ ∘ fnoc) cons conf

ChoiceConstructor : ∀ (F : 𝔽) → VariabilityConstruct
ChoiceConstructor F = Variational-⟪ 2Choice F , 2Config F , 2Choice-sem F ⟫

module Embed
  {F : 𝔽} {A : 𝔸}
  (Γ : VariabilityLanguage)
  (constr : ChoiceConstructor F ⟦∈⟧ᵥ Γ)
  where

  extr = extract constr

  open Choice-to-2Choice.Translate {F} (Expression Γ A)
  open Data.IndexedSet (Eq.setoid (Variant A)) using (_≅_; ≗→≅)

  embed : ∀ {i} → NestedChoice i (Expression Γ A) → Expression Γ A
  embed (value v) = v
  embed (choice c) = cons (make constr) (2Choice.map embed c)

  embed-preserves : ∀ {i}
    → (e : NestedChoice i (Expression Γ A))
    → Semantics Γ (embed e) ≅ λ c → Semantics Γ (⟦ e ⟧ (extr c)) c
  embed-preserves e = ≗→≅ (induction e)
    where
    induction : ∀ {i}
      → (e : NestedChoice i (Expression Γ A))
      → Semantics Γ (embed e) ≗ λ c → Semantics Γ (⟦ e ⟧ (extr c)) c
    induction (value v) c = refl
    induction (choice (dim ⟨ l , r ⟩)) c
      rewrite preservation constr (dim ⟨ embed l , embed r ⟩) c
      with evalConfig (extr c) dim
    ... | true = induction l c
    ... | false = induction r c
