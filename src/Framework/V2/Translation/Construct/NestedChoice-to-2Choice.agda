{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Framework.V2.Translation.Construct.NestedChoice-to-2Choice where

open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; proj₁; Σ-syntax) renaming (_,_ to _and_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
import Relation.Binary.PropositionalEquality as Eq

import Data.IndexedSet

open import Function.Base using (id; _∘_)

open import Framework.V2.Definitions
open import Framework.V2.VariabilityLanguage
open import Framework.V2.Construct
open import Framework.V2.Annotation.IndexedName using (IndexedName)
import Framework.V2.Constructs.Choices as Chc
open Chc.Choiceₙ using () renaming (Config to Configₙ)
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Config to Config₂)
open Chc.VLChoice₂ using () renaming (Syntax to Choice₂; Semantics to Choice₂-sem)

import Framework.V2.Translation.Construct.NChoice-to-2Choice as NChoice-to-2Choice
open NChoice-to-2Choice using (NestedChoice; value; choice; evalConfig)
module NChoice-to-2Choice-explicit Q = NChoice-to-2Choice {Q}
open NChoice-to-2Choice-explicit using (2Config)

2Choice : 𝔽 → ℂ
2Choice F E A = Choice₂ (IndexedName F) E A

2Choice-sem : ∀ (V : 𝕍) (F : 𝔽) → VariationalConstruct-Semantics V (2Config F) (2Choice F)
2Choice-sem V F Γ fnoc cons conf = Choice₂-sem V (IndexedName F) Γ (proj₁ ∘ fnoc) cons conf

ChoiceConstructor : ∀ (V : 𝕍) (F : 𝔽) → VariabilityConstruct V
ChoiceConstructor V F = Variational-⟪ 2Choice F , 2Config F , 2Choice-sem V F ⟫

module Embed
  {V : 𝕍} {F : 𝔽} {A : 𝔸}
  (Γ : VariabilityLanguage V)
  (constr : ChoiceConstructor V F ⟦∈⟧ᵥ Γ)
  where

  extr = extract constr

  open NChoice-to-2Choice.Translate {F} (Eq.setoid (Expression Γ A))
  open Data.IndexedSet (Eq.setoid (V A)) using (_≅_; ≗→≅)

  embed : ∀ {i} → NestedChoice i (Expression Γ A) → Expression Γ A
  embed (value v) = v
  embed (choice c) = cons (make constr) (map embed c)
    where
    open Chc.Choice₂ using (map)

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
