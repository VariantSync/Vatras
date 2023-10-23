{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Translation.NChoice-to-2Choice-Test (F : 𝔽) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Framework.V2.Compiler using (ConstructCompiler)
open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)
open Chc.VLChoice₂ using () renaming (Construct to C₂)
open Chc.VLChoiceₙ using () renaming (Construct to Cₙ)

open import Framework.V2.Translation.NChoice-to-2Choice {Q = F} as BLUB
module Trans = BLUB.Translate ℕ
open Trans
open IndexedDimension

example : ∀ {D : F} → D ⟨ 1 , 2 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , val 2 ⟩) ⟩
example = step base

example' : ∀ {D : F}
  → D ⟨ 1 , 2 ∷ 3 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , chc ((D ∙ 2) ⟨ val 3 , val 3 ⟩) ⟩) ⟩
example' = step (step base)

module Pres = Trans.Preservation
open Pres

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
import Data.IndexedSet
module ISN = Data.IndexedSet (Eq.setoid ℕ)
open ISN using (_∈_at_; _⊆[_]_; _≅[_][_]_)

Conf : ∀ {ℓ} (Q : Set ℓ) → Set ℓ
Conf Q = Configₙ Q → Config₂ (IndexedDimension Q)

Fnoc : ∀ {ℓ} (Q : Set ℓ) → Set ℓ
Fnoc Q = Config₂ (IndexedDimension Q) → Configₙ Q

un-conf : ∀ {ℓ} {Q : Set ℓ} → Conf Q
un-conf cₙ (D ∙ i) = true

un-fnoc : ∀ {ℓ} {Q : Set ℓ} → Fnoc Q
un-fnoc c₂ D = 0

un : ∀ {D : F} → Preserved (D ⟨ 1 ∷ [] ⟩) un-conf un-fnoc
proj₁ (un {D}) c with c D in eq
... | zero = refl
... | suc x = refl
proj₂ (un {D}) c with c (D ∙ 0) in eq
... | false = refl
... | true = refl

bi-conf : ∀ {ℓ} {Q : Set ℓ} → Conf Q
bi-conf cₙ (D ∙ i) with cₙ D
... | zero = true
... | suc x = false

bi-fnoc : ∀ {ℓ} {Q : Set ℓ} → Fnoc Q
bi-fnoc c₂ D with c₂ (D ∙ 0)
... | false = 1
... | true = 0

bi : ∀ {D : F} → Preserved (D ⟨ 1 ∷ 2 ∷ [] ⟩) bi-conf bi-fnoc
proj₁ (bi {D}) c with c D
... | zero = refl
... | suc x with bi-conf c (D ∙ 1)
...         | false = refl
...         | true  = refl
proj₂ (bi {D}) c with c (D ∙ 0)
... | true = refl
... | false with c (D ∙ 1)
...         | false = refl
...         | true  = refl
