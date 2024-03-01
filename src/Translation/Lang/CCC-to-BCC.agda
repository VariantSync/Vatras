{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.CCC-to-BCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

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

open import Translation.Lang.CCC-to-FCC Variant Artifact∈ₛVariant using (maxChoiceLength; maxChoiceLengthIsLimit) renaming (translate to CCC→FCC; conf to CCCꟲ→FCCꟲ; fnoc to CCCꟲ→FCCꟲ⁻¹; preserves to CCC→FCC-preserves)
open import Translation.Lang.FCC-to-BCC Variant Artifact∈ₛVariant using () renaming (translate to FCC→BCC; conf to FCCꟲ→BCCꟲ; fnoc to FCCꟲ→BCCꟲ⁻¹; preserves to FCC→BCC-preserves)
open import Translation.Lang.BCC-to-BCC Variant Artifact∈ₛVariant using () renaming (map-dim to BCC-map-dim; preserves to BCC-map-dim-preserves)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


Fin→ℕ : {D : Set} → (n : ℕ≥ 2) -> D × Fin (ℕ≥.toℕ (ℕ≥.pred n)) → D × ℕ
Fin→ℕ n (d , i) = (d , Fin.toℕ i)

Fin→ℕ⁻¹ : {D : Set} → (n : ℕ≥ 2) -> D × ℕ → D × Fin (ℕ≥.toℕ (ℕ≥.pred n))
Fin→ℕ⁻¹ n (d , i) = (d , ℕ≥.cappedFin {ℕ≥.pred n} i)

translate : {D A : Set} → CCC D ∞ A → BCC (D × ℕ) ∞ A
translate expr = BCC-map-dim (Fin→ℕ n) (FCC→BCC n (CCC→FCC n expr (maxChoiceLengthIsLimit expr)))
  where
  n = maxChoiceLength expr

conf : {D : Set} → ℕ≥ 2 → CCCꟲ D → BCCꟲ (D × ℕ)
conf n = (_∘ Fin→ℕ⁻¹ n) ∘ FCCꟲ→BCCꟲ n ∘ CCCꟲ→FCCꟲ n

fnoc : {D : Set} → ℕ≥ 2 → BCCꟲ (D × ℕ) → CCCꟲ D
fnoc n = CCCꟲ→FCCꟲ⁻¹ n ∘ FCCꟲ→BCCꟲ⁻¹ n ∘ (_∘ Fin→ℕ n)

preserves : {D A : Set} → (expr : CCC D ∞ A) → ⟦ translate expr ⟧₂ ≅[ fnoc (maxChoiceLength expr) ][ conf (maxChoiceLength expr) ] ⟦ expr ⟧ₐ
preserves expr =
  ⟦ translate expr ⟧₂
  ≅[]⟨⟩
  ⟦ BCC-map-dim (Fin→ℕ n) (FCC→BCC n (CCC→FCC n expr (maxChoiceLengthIsLimit expr))) ⟧₂
  ≅[]⟨ BCC-map-dim-preserves (Fin→ℕ n) (Fin→ℕ⁻¹ n) (λ where (d , i) → Eq.cong₂ _,_ refl (lemma n i)) (FCC→BCC n (CCC→FCC n expr (maxChoiceLengthIsLimit expr))) ⟩
  ⟦ FCC→BCC n (CCC→FCC n expr (maxChoiceLengthIsLimit expr)) ⟧₂
  ≅[]⟨ FCC→BCC-preserves n (CCC→FCC n expr (maxChoiceLengthIsLimit expr)) ⟩
  ⟦ CCC→FCC n expr (maxChoiceLengthIsLimit expr) ⟧ₙ
  ≅[]⟨ CCC→FCC-preserves n expr (maxChoiceLengthIsLimit expr) ⟩
  ⟦ expr ⟧ₐ
  ≅[]-∎
  where
  n = maxChoiceLength expr
  lemma : (n : ℕ≥ 2) → (i : Fin (ℕ≥.toℕ (ℕ≥.pred n))) → ℕ≥.cappedFin {ℕ≥.pred n} (Fin.toℕ i) ≡ i
  lemma (sucs n) i = ℕ≥.cappedFin-toℕ i
