{-# OPTIONS --sized-types #-}
module Translation.Lang.FCC-to-CCC where

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

open import Lang.Choices
open import Lang.CCC renaming (Configuration to CCCꟲ)
module CCCSem {A} = Lang.CCC.Sem A Variant Artifact∈ₛVariant
open CCCSem using () renaming (⟦_⟧ to ⟦_⟧ₐ)


translate : {i : Size} → {n : ℕ≥ 2} -> {D A : Set} → NAryChoice n D A {i} → CCC D ∞ A
translate (artifact a cs) = a -< List.map translate cs >-
translate {n = sucs n} (choice d (c ∷ cs)) = d ⟨ List⁺.fromVec (Vec.map translate (c ∷ cs)) ⟩

conf : {D : Set} → (n : ℕ≥ 2) → NAryChoiceConfig n D → CCCꟲ D
conf (sucs n) config d = Fin.toℕ (config d)

fnoc : {D : Set} → (n : ℕ≥ 2) → CCCꟲ D → NAryChoiceConfig n D
fnoc (sucs n) config d = ℕ≥.cappedFin (config d)


preserves-⊆ : ∀ {i : Size} {D A : Set} (n : ℕ≥ 2)
  → (expr : NAryChoice n D A {i})
  → ⟦ translate expr ⟧ₐ ⊆[ fnoc n ] ⟦ expr ⟧ₙ
preserves-⊆ n (artifact a cs) config =
  ⟦ translate (artifact a cs) ⟧ₐ config
  ≡⟨⟩
  ⟦ a -< List.map translate cs >- ⟧ₐ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ config) (List.map translate cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ config)} {f = translate} cs) ⟩
  artifact a (List.map (λ e → ⟦ translate e ⟧ₐ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc n config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧ₙ (fnoc n config)
  ∎
preserves-⊆ (sucs n) (choice d (c ∷ cs)) config =
  ⟦ translate (choice d (c ∷ cs)) ⟧ₐ config
  ≡⟨⟩
  ⟦ d ⟨ List⁺.fromVec (Vec.map translate (c ∷ cs)) ⟩ ⟧ₐ config
  ≡⟨⟩
  ⟦ find-or-last (config d) (List⁺.fromVec (Vec.map translate (c ∷ cs))) ⟧ₐ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = config d} (translate c ∷ Vec.map translate cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map translate (c ∷ cs)) (ℕ≥.cappedFin (config d)) ⟧ₐ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (ℕ≥.cappedFin (config d)) translate (c ∷ cs)) refl ⟩
  ⟦ translate (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) ⟧ₐ config
  ≡⟨ preserves-⊆ (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) config ⟩
  ⟦ Vec.lookup (c ∷ cs) (fnoc (sucs n) config d) ⟧ₙ (fnoc (sucs n) config)
  ≡⟨⟩
  ⟦ choice d (c ∷ cs) ⟧ₙ (fnoc (sucs n) config)
  ∎

preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A {i}) → ⟦ expr ⟧ₙ ⊆[ conf n ] ⟦ translate expr ⟧ₐ
preserves-⊇ n (artifact a cs) config =
  ⟦ artifact a cs ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ translate e ⟧ₐ (conf n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ (conf n config))} {f = translate} cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ (conf n config)) (List.map translate cs))
  ≡⟨⟩
  ⟦ a -< List.map translate cs >- ⟧ₐ (conf n config)
  ≡⟨⟩
  ⟦ translate (artifact a cs) ⟧ₐ (conf n config)
  ∎
preserves-⊇ {D} {A} (sucs n) (choice d (c ∷ cs)) config =
  ⟦ choice d (c ∷ cs) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (c ∷ cs) (config d) ⟧ₙ config
  ≡⟨ preserves-⊇ (sucs n) (Vec.lookup (c ∷ cs) (config d)) config ⟩
  ⟦ translate (Vec.lookup (c ∷ cs) (config d)) ⟧ₐ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (config d) translate (c ∷ cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map translate (c ∷ cs)) (config d) ⟧ₐ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Eq.cong₂ Vec.lookup (refl {x = Vec.map translate (c ∷ cs)}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
  ⟦ Vec.lookup (Vec.map translate (c ∷ cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₐ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = Fin.toℕ (config d)} (translate c ∷ Vec.map translate cs)) refl ⟩
  ⟦ find-or-last (Fin.toℕ (config d)) (List⁺.fromVec (Vec.map translate (c ∷ cs))) ⟧ₐ (conf (sucs n) config)
  ≡⟨⟩
  ⟦ d ⟨ List⁺.fromVec (Vec.map translate (c ∷ cs)) ⟩ ⟧ₐ (conf (sucs n) config)
  ≡⟨⟩
  ⟦ translate (choice d (c ∷ cs)) ⟧ₐ (conf (sucs n) config)
  ∎

preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A) → ⟦ translate expr ⟧ₐ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₙ
preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr
