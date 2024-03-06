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
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ↑_; ∞)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.CCC renaming (Configuration to CCCꟲ)
open Lang.CCC.Sem using (CCCL)
module CCCSem {A} = Lang.CCC.Sem A Variant Artifact∈ₛVariant
open CCCSem using () renaming (⟦_⟧ to ⟦_⟧ₐ)

import Lang.FCC
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

import Lang.BCC
module BCC n = Lang.BCC n
open BCC renaming (Configuration to BCCꟲ)
open Lang.BCC.Sem using (BCCL)
module BCCSem {A} = Lang.BCC.Sem A Variant Artifact∈ₛVariant
open BCCSem using () renaming (⟦_⟧ to ⟦_⟧₂)

import Translation.Lang.BCC-to-FCC
open Translation.Lang.BCC-to-FCC.2Ary Variant Artifact∈ₛVariant using (BCC→FCC)
open import Translation.Lang.FCC-to-CCC Variant Artifact∈ₛVariant using (FCC→CCC)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


BCC→CCC : {i : Size} → {D : Set} → LanguageCompiler (BCCL D Variant Artifact∈ₛVariant {i}) (CCCL D Variant Artifact∈ₛVariant)
BCC→CCC = BCC→FCC ⊕ FCC→CCC (sucs zero)

CCC≽BCC : {D : Set} → CCCL D Variant Artifact∈ₛVariant ≽ BCCL D Variant Artifact∈ₛVariant
CCC≽BCC = expressiveness-from-compiler BCC→CCC
