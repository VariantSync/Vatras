{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.BCC-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ↑_; ∞)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.CCC renaming (Configuration to CCCꟲ)
module CCCSem {A} = Lang.CCC.Sem A Variant Artifact∈ₛVariant
open CCCSem using () renaming (⟦_⟧ to ⟦_⟧ₐ)

import Lang.FCC
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

import Lang.BCC
module BCC n = Lang.BCC n
open BCC renaming (Configuration to BCCꟲ)
module BCCSem {A} = Lang.BCC.Sem A Variant Artifact∈ₛVariant
open BCCSem using () renaming (⟦_⟧ to ⟦_⟧₂)

open import Translation.Lang.BCC-to-FCC Variant Artifact∈ₛVariant using () renaming (translate to BCC→FCC; conf to BCCꟲ→FCCꟲ; fnoc to BCCꟲ→FCCꟲ⁻¹; preserves to BCC→FCC-preserves)
open import Translation.Lang.FCC-to-CCC Variant Artifact∈ₛVariant using () renaming (translate to FCC→CCC; conf to FCCꟲ→CCCꟲ; fnoc to FCCꟲ→CCCꟲ⁻¹; preserves to FCC→CCC-preserves)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


translate : {i : Size} → {D A : Set} → BCC D i A → CCC D ∞ A
translate expr = FCC→CCC (sucs zero) (BCC→FCC expr)

conf : {D : Set} → BCCꟲ D → CCCꟲ D
conf = FCCꟲ→CCCꟲ (sucs zero) ∘ BCCꟲ→FCCꟲ

fnoc : {D : Set} → CCCꟲ D → BCCꟲ D
fnoc = BCCꟲ→FCCꟲ⁻¹ ∘ FCCꟲ→CCCꟲ⁻¹ (sucs zero)

preserves : {i : Size} → {D A : Set} → (expr : BCC D i A) → ⟦ translate expr ⟧ₐ ≅[ fnoc ][ conf ] ⟦ expr ⟧₂
preserves expr =
  ⟦ translate expr ⟧ₐ
  ≅[]⟨⟩
  ⟦ FCC→CCC (sucs zero) (BCC→FCC expr) ⟧ₐ
  ≅[]⟨ FCC→CCC-preserves (sucs zero) (BCC→FCC expr) ⟩
  ⟦ BCC→FCC expr ⟧ₙ
  ≅[]⟨ BCC→FCC-preserves expr ⟩
  ⟦ expr ⟧₂
  ≅[]-∎
