{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.FCC-to-BCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (push-function-into-if)
open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_) renaming (_,_ to _and_)
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

open import Lang.BCC renaming (Configuration to BCCꟲ)
module BCCSem {A} = Lang.BCC.Sem A Variant Artifact∈ₛVariant
open BCCSem using () renaming (⟦_⟧ to ⟦_⟧₂)

import Lang.FCC
module FCC n = Lang.FCC n
open FCC renaming (Configuration to FCCꟲ)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Translation.Lang.FCC-to-FCC Variant Artifact∈ₛVariant using () renaming (translate to FCC→FCC; conf to FCCꟲ→FCCꟲ; fnoc to FCCꟲ→FCCꟲ⁻¹; preserves to FCC→FCC-preserves)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module 2Ary where
  translate : {i : Size} → {D A : Set} → FCC (sucs zero) D i A → BCC D ∞ A
  translate (a -< cs >-) = a -< List.map translate cs >-
  translate (d ⟨ l ∷ r ∷ [] ⟩) = d ⟨ translate l , translate r ⟩

  conf : {D : Set} → FCCꟲ (sucs zero) D → BCCꟲ D
  conf config d with config d
  ... | zero = true
  ... | suc zero = false

  fnoc : {D : Set} → BCCꟲ D → FCCꟲ (sucs zero) D
  fnoc config d with config d
  ... | true = zero
  ... | false = suc zero

  preserves-⊆ : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ translate expr ⟧₂ ⊆[ fnoc ] ⟦ expr ⟧ₙ
  preserves-⊆ (a -< cs >-) config =
    ⟦ translate (a -< cs >-) ⟧₂ config
    ≡⟨⟩
    ⟦ (a -< List.map translate cs >-) ⟧₂ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map translate cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧₂ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc config)) cs)
    ≡⟨⟩
    ⟦ a -< cs >- ⟧ₙ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l ∷ r ∷ [] ⟩) config =
    ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ config
    ≡⟨⟩
    ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ config
    ≡⟨⟩
    ⟦ if config d then translate l else translate r ⟧₂ config
    ≡⟨ push-function-into-if (λ e → ⟦ e ⟧₂ config) (config d) ⟩
    (if config d then ⟦ translate l ⟧₂ config else ⟦ translate r ⟧₂ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (config d)) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
    (if config d then ⟦ l ⟧ₙ (fnoc config) else ⟦ r ⟧ₙ (fnoc config))
    ≡⟨ lemma ⟩
    Vec.lookup (⟦ l ⟧ₙ (fnoc config) ∷ ⟦ r ⟧ₙ (fnoc config) ∷ []) (fnoc config d)
    ≡⟨ Vec.lookup-map (fnoc config d) (λ e → ⟦ e ⟧ₙ (fnoc config)) (l ∷ r ∷ []) ⟩
    ⟦ Vec.lookup (l ∷ r ∷ []) (fnoc config d) ⟧ₙ (fnoc config)
    ≡⟨⟩
    ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ (fnoc config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (fnoc config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves-⊇ : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ expr ⟧ₙ ⊆[ conf ] ⟦ translate expr ⟧₂
  preserves-⊇ (a -< cs >-) config =
    ⟦ a -< cs >- ⟧ₙ config
    ≡⟨⟩
    artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
    artifact a (List.map (λ e → ⟦ translate e ⟧₂ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → ⟦ e ⟧₂ (conf config)) (List.map translate cs))
    ≡⟨⟩
    ⟦ (a -< List.map translate cs >-) ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ translate (a -< cs >-) ⟧₂ (conf config)
    ∎
  preserves-⊇ (d ⟨ l ∷ r ∷ [] ⟩) config =
    ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ config
    ≡⟨⟩
    ⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧ₙ config
    ≡˘⟨ Vec.lookup-map (config d) (λ e → ⟦ e ⟧ₙ config) (l ∷ r ∷ []) ⟩
    Vec.lookup (⟦ l ⟧ₙ config ∷ ⟦ r ⟧ₙ config ∷ []) (config d)
    ≡⟨ lemma ⟩
    (if conf config d then ⟦ l ⟧ₙ config else ⟦ r ⟧ₙ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (conf config d)) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
    (if conf config d then ⟦ translate l ⟧₂ (conf config) else ⟦ translate r ⟧₂ (conf config))
    ≡˘⟨ push-function-into-if (λ e → ⟦ e ⟧₂ (conf config)) (conf config d) ⟩
    ⟦ if conf config d then translate l else translate r ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ (conf config)
    ≡⟨⟩
    ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ (conf config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if conf config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves : {i : Size} → {D A : Set} → (expr : FCC (sucs zero) D i A) → ⟦ translate expr ⟧₂ ≅[ fnoc ][ conf ] ⟦ expr ⟧ₙ
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

conf : {D : Set} → (n : ℕ≥ 2) → FCCꟲ n D → BCCꟲ (D × Fin (ℕ≥.toℕ (ℕ≥.pred n)))
conf n = 2Ary.conf ∘ FCCꟲ→FCCꟲ n (sucs zero)

fnoc : {D : Set} → (n : ℕ≥ 2) → BCCꟲ (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) → FCCꟲ n D
fnoc n = FCCꟲ→FCCꟲ⁻¹ n (sucs zero) ∘ 2Ary.fnoc

translate : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → FCC n D i A → BCC (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) ∞ A
translate n expr = 2Ary.translate (FCC→FCC n (sucs zero) expr)

preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ translate n expr ⟧₂ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₙ
preserves n expr =
  ⟦ translate n expr ⟧₂
  ≅[]⟨⟩
  ⟦ 2Ary.translate (FCC→FCC n (sucs zero) expr) ⟧₂
  ≅[]⟨ 2Ary.preserves (FCC→FCC n (sucs zero) expr) ⟩
  ⟦ FCC→FCC n (sucs zero) expr ⟧ₙ
  ≅[]⟨ FCC→FCC-preserves n (sucs zero) expr ⟩
  ⟦ expr ⟧ₙ
  ≅[]-∎
