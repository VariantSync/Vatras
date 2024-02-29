{-# OPTIONS --sized-types #-}
module Translation.Lang.CCC-to-BCC where

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

import Lang.FCC
module FCC n = Lang.FCC n
open FCC renaming (Configuration to FCCꟲ)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Translation.Lang.CCC-to-FCC using (maxChoiceLength; maxChoiceLengthIsLimit) renaming (translate to CCC→FCC; conf to CCCꟲ→FCCꟲ; fnoc to CCCꟲ→FCCꟲ⁻¹; preserves to CCC→FCC-preserves)
import Translation.Lang.FCC-to-FCC
open Translation.Lang.FCC-to-FCC.DecreaseArity using () renaming (translate to FCC→BCC; conf to FCCꟲ→BCCꟲ; fnoc to FCCꟲ→BCCꟲ⁻¹; preserves to FCC→BCC-preserves)

FCC-map-dimension : {i : Size} → {n : ℕ≥ 2} → {D A D' : Set} → (D → D') → FCC n D i A → FCC n D' i A
FCC-map-dimension f (a -< cs >-) = a -< List.map (FCC-map-dimension f) cs >-
FCC-map-dimension f (d ⟨ cs ⟩) = f d ⟨ Vec.map (FCC-map-dimension f) cs ⟩

BCC-Fin⇒ℕ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → FCC (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) i A → FCC (sucs zero) (D × ℕ) i A
BCC-Fin⇒ℕ n = FCC-map-dimension (λ (d , i) → d , Fin.toℕ i)


translate : {D A : Set} → CCC D ∞ A → FCC (sucs zero) (D × ℕ) ∞ A
translate expr = BCC-Fin⇒ℕ (maxChoiceLength expr) (FCC→BCC (maxChoiceLength expr) (CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)))


BCCꟲ-Fin⇒ℕ : {D : Set} → (n : ℕ≥ 2) → FCCꟲ (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) → FCCꟲ (sucs zero) (D × ℕ)
BCCꟲ-Fin⇒ℕ (sucs n) config (d , i) = config (d , ℕ≥.cappedFin i)

BCCꟲ-Fin⇒ℕ⁻¹ : {D : Set} → (n : ℕ≥ 2) → FCCꟲ (sucs zero) (D × ℕ) → FCCꟲ (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n)))
BCCꟲ-Fin⇒ℕ⁻¹ n config (d , i) = config (d , Fin.toℕ i)

BCC-Fin⇒ℕ-preserves-⊆ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) i A) → ⟦ BCC-Fin⇒ℕ n expr ⟧ₙ ⊆[ BCCꟲ-Fin⇒ℕ⁻¹ n ] ⟦ expr ⟧ₙ
BCC-Fin⇒ℕ-preserves-⊆ n (a -< cs >-) config =
  ⟦ BCC-Fin⇒ℕ n (a -< cs >-) ⟧ₙ config
  ≡⟨⟩
  ⟦ a -< List.map (FCC-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs >- ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map (FCC-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ FCC-map-dimension (λ (d , i) → d , Fin.toℕ i) e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → BCC-Fin⇒ℕ-preserves-⊆ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (BCCꟲ-Fin⇒ℕ⁻¹ n config)) cs)
  ≡⟨⟩
  ⟦ a -< cs >- ⟧ₙ (BCCꟲ-Fin⇒ℕ⁻¹ n config)
  ∎
BCC-Fin⇒ℕ-preserves-⊆ n ((d , i) ⟨ cs ⟩) config =
  ⟦ BCC-Fin⇒ℕ n ((d , i) ⟨ cs ⟩) ⟧ₙ config
  ≡⟨⟩
  ⟦ (d , Fin.toℕ i) ⟨ Vec.map (BCC-Fin⇒ℕ n) cs ⟩ ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.map (BCC-Fin⇒ℕ n) cs) (config (d , Fin.toℕ i)) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config (d , Fin.toℕ i)) (BCC-Fin⇒ℕ n) cs) refl ⟩
  ⟦ BCC-Fin⇒ℕ n (Vec.lookup cs (config (d , Fin.toℕ i))) ⟧ₙ config
  ≡⟨ BCC-Fin⇒ℕ-preserves-⊆ n (Vec.lookup cs (config (d , Fin.toℕ i))) config ⟩
  ⟦ Vec.lookup cs (config (d , Fin.toℕ i)) ⟧ₙ (BCCꟲ-Fin⇒ℕ⁻¹ n config)
  ≡⟨⟩
  ⟦ Vec.lookup cs (BCCꟲ-Fin⇒ℕ⁻¹ n config (d , i)) ⟧ₙ (BCCꟲ-Fin⇒ℕ⁻¹ n config)
  ≡⟨⟩
  ⟦ (d , i) ⟨ cs ⟩ ⟧ₙ (BCCꟲ-Fin⇒ℕ⁻¹ n config)
  ∎


BCC-Fin⇒ℕ-preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) i A) → ⟦ expr ⟧ₙ ⊆[ BCCꟲ-Fin⇒ℕ n ] ⟦ BCC-Fin⇒ℕ n expr ⟧ₙ
BCC-Fin⇒ℕ-preserves-⊇ n (a -< cs >-) config =
  ⟦ a -< cs >- ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → BCC-Fin⇒ℕ-preserves-⊇ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ FCC-map-dimension (λ (d , i) → d , Fin.toℕ i) e ⟧ₙ (BCCꟲ-Fin⇒ℕ n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (BCCꟲ-Fin⇒ℕ n config)) (List.map (FCC-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs))
  ≡⟨⟩
  ⟦ a -< List.map (FCC-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs >- ⟧ₙ (BCCꟲ-Fin⇒ℕ n config)
  ≡⟨⟩
  ⟦ BCC-Fin⇒ℕ n (a -< cs >-) ⟧ₙ (BCCꟲ-Fin⇒ℕ n config)
  ∎
BCC-Fin⇒ℕ-preserves-⊇ (sucs n) ((d , i) ⟨ cs ⟩) config =
  ⟦ (d , i) ⟨ cs ⟩ ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (config (d , i)) ⟧ₙ config
  ≡˘⟨ Eq.cong₂ (⟦_⟧ₙ) {u = config} (Eq.cong₂ Vec.lookup {x = cs} refl (Eq.cong config (Eq.cong₂ _,_ refl (ℕ≥.cappedFin-toℕ i)))) refl ⟩
  ⟦ Vec.lookup cs (config (d , ℕ≥.cappedFin (Fin.toℕ i))) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (BCCꟲ-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) ⟧ₙ config
  ≡⟨ BCC-Fin⇒ℕ-preserves-⊇ (sucs n) (Vec.lookup cs (BCCꟲ-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i))) config ⟩
  ⟦ BCC-Fin⇒ℕ (sucs n) (Vec.lookup cs (BCCꟲ-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i))) ⟧ₙ (BCCꟲ-Fin⇒ℕ (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (BCCꟲ-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) (BCC-Fin⇒ℕ (sucs n)) cs) refl ⟩
  ⟦ Vec.lookup (Vec.map (BCC-Fin⇒ℕ (sucs n)) cs) (BCCꟲ-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) ⟧ₙ (BCCꟲ-Fin⇒ℕ (sucs n) config)
  ≡⟨⟩
  ⟦ (d , Fin.toℕ i) ⟨ Vec.map (BCC-Fin⇒ℕ (sucs n)) cs ⟩ ⟧ₙ (BCCꟲ-Fin⇒ℕ (sucs n) config)
  ≡⟨⟩
  ⟦ BCC-Fin⇒ℕ (sucs n) ((d , i) ⟨ cs ⟩) ⟧ₙ (BCCꟲ-Fin⇒ℕ (sucs n) config)
  ∎

BCC-Fin⇒ℕ-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : FCC (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) ∞ A) → ⟦ BCC-Fin⇒ℕ n expr ⟧ₙ ≅[ BCCꟲ-Fin⇒ℕ⁻¹ n ][ BCCꟲ-Fin⇒ℕ n ] ⟦ expr ⟧ₙ
BCC-Fin⇒ℕ-preserves n expr = BCC-Fin⇒ℕ-preserves-⊆ n expr , BCC-Fin⇒ℕ-preserves-⊇ n expr


conf : {D : Set} → ℕ≥ 2 → CCCꟲ D → FCCꟲ (sucs zero) (D × ℕ)
conf n = BCCꟲ-Fin⇒ℕ n ∘ FCCꟲ→BCCꟲ n ∘ CCCꟲ→FCCꟲ n

fnoc : {D : Set} → ℕ≥ 2 → FCCꟲ (sucs zero) (D × ℕ) → CCCꟲ D
fnoc n = CCCꟲ→FCCꟲ⁻¹ n ∘ FCCꟲ→BCCꟲ⁻¹ n ∘ BCCꟲ-Fin⇒ℕ⁻¹ n

preserves : {D A : Set} → (expr : CCC D ∞ A) → ⟦ translate expr ⟧ₙ ≅[ fnoc (maxChoiceLength expr) ][ conf (maxChoiceLength expr) ] ⟦ expr ⟧ₐ
preserves expr =
  ⟦ translate expr ⟧ₙ
  ≅[]⟨⟩
  ⟦ BCC-Fin⇒ℕ (maxChoiceLength expr) (FCC→BCC (maxChoiceLength expr) (CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr))) ⟧ₙ
  ≅[]⟨ BCC-Fin⇒ℕ-preserves (maxChoiceLength expr) (FCC→BCC (maxChoiceLength expr) (CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr))) ⟩
  ⟦ FCC→BCC (maxChoiceLength expr) (CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)) ⟧ₙ
  ≅[]⟨ FCC→BCC-preserves (maxChoiceLength expr) (CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)) ⟩
  ⟦ CCC→FCC (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr) ⟧ₙ
  ≅[]⟨ CCC→FCC-preserves (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr) ⟩
  ⟦ expr ⟧ₐ
  ≅[]-∎
