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

open import Translation.Lang.CCC-to-FCC using (maxChoiceLength; maxChoiceLengthIsLimit) renaming (translate to CCC→NAryChoice; conf to CCCꟲ→NAryChoiceConfig; fnoc to CCCꟲ→NAryChoiceConfig⁻¹; preserves to CCC→NAryChoice-preserves)
import Translation.Lang.FCC-to-FCC
open Translation.Lang.FCC-to-FCC.DecreaseArity using () renaming (translate to NAryChoice→2AryChoice; conf to NAryChoiceConfig→2AryChoiceConfig; fnoc to NAryChoiceConfig→2AryChoiceConfig⁻¹; preserves to NAryChoice→2AryChoice-preserves)

NAryChoice-map-dimension : {i : Size} → {n : ℕ≥ 2} → {D A D' : Set} → (D → D') → NAryChoice n D A {i} → NAryChoice n D' A {i}
NAryChoice-map-dimension f (artifact a cs) = artifact a (List.map (NAryChoice-map-dimension f) cs)
NAryChoice-map-dimension f (choice d cs) = choice (f d) (Vec.map (NAryChoice-map-dimension f) cs)

2AryChoice-Fin⇒ℕ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → 2AryChoice (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A {i} → 2AryChoice (D × ℕ) A {i}
2AryChoice-Fin⇒ℕ n = NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i)


translate : {D A : Set} → CCC D ∞ A → 2AryChoice (D × ℕ) A
translate expr = 2AryChoice-Fin⇒ℕ (maxChoiceLength expr) (NAryChoice→2AryChoice (maxChoiceLength expr) (CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)))


2AryChoiceConfig-Fin⇒ℕ : {D : Set} → (n : ℕ≥ 2) → 2AryChoiceConfig (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) → 2AryChoiceConfig (D × ℕ)
2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , i) = config (d , ℕ≥.cappedFin i)

2AryChoiceConfig-Fin⇒ℕ⁻¹ : {D : Set} → (n : ℕ≥ 2) → 2AryChoiceConfig (D × ℕ) → 2AryChoiceConfig (D × Fin (ℕ≥.toℕ (ℕ≥.pred n)))
2AryChoiceConfig-Fin⇒ℕ⁻¹ n config (d , i) = config (d , Fin.toℕ i)

2AryChoice-Fin⇒ℕ-preserves-⊆ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : 2AryChoice (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A {i}) → ⟦ 2AryChoice-Fin⇒ℕ n expr ⟧₂ ⊆[ 2AryChoiceConfig-Fin⇒ℕ⁻¹ n ] ⟦ expr ⟧₂
2AryChoice-Fin⇒ℕ-preserves-⊆ n (artifact a cs) config =
  ⟦ 2AryChoice-Fin⇒ℕ n (artifact a cs) ⟧₂ config
  ≡⟨⟩
  ⟦ artifact a (List.map (NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs) ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map (NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i) e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → 2AryChoice-Fin⇒ℕ-preserves-⊆ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧₂ (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config)
  ∎
2AryChoice-Fin⇒ℕ-preserves-⊆ n (choice (d , i) cs) config =
  ⟦ 2AryChoice-Fin⇒ℕ n (choice (d , i) cs) ⟧₂ config
  ≡⟨⟩
  ⟦ choice (d , Fin.toℕ i) (Vec.map (2AryChoice-Fin⇒ℕ n) cs) ⟧₂ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.map (2AryChoice-Fin⇒ℕ n) cs) (config (d , Fin.toℕ i)) ⟧₂ config
  ≡⟨ Eq.cong₂ ⟦_⟧₂ (Vec.lookup-map (config (d , Fin.toℕ i)) (2AryChoice-Fin⇒ℕ n) cs) refl ⟩
  ⟦ 2AryChoice-Fin⇒ℕ n (Vec.lookup cs (config (d , Fin.toℕ i))) ⟧₂ config
  ≡⟨ 2AryChoice-Fin⇒ℕ-preserves-⊆ n (Vec.lookup cs (config (d , Fin.toℕ i))) config ⟩
  ⟦ Vec.lookup cs (config (d , Fin.toℕ i)) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config)
  ≡⟨⟩
  ⟦ Vec.lookup cs (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config (d , i)) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config)
  ≡⟨⟩
  ⟦ choice (d , i) cs ⟧₂ (2AryChoiceConfig-Fin⇒ℕ⁻¹ n config)
  ∎


2AryChoice-Fin⇒ℕ-preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : 2AryChoice (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A {i}) → ⟦ expr ⟧₂ ⊆[ 2AryChoiceConfig-Fin⇒ℕ n ] ⟦ 2AryChoice-Fin⇒ℕ n expr ⟧₂
2AryChoice-Fin⇒ℕ-preserves-⊇ n (artifact a cs) config =
  ⟦ artifact a cs ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → 2AryChoice-Fin⇒ℕ-preserves-⊇ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i) e ⟧₂ (2AryChoiceConfig-Fin⇒ℕ n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ (2AryChoiceConfig-Fin⇒ℕ n config)) (List.map (NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs))
  ≡⟨⟩
  ⟦ artifact a (List.map (NAryChoice-map-dimension (λ (d , i) → d , Fin.toℕ i)) cs) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ n config)
  ≡⟨⟩
  ⟦ 2AryChoice-Fin⇒ℕ n (artifact a cs) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ n config)
  ∎
2AryChoice-Fin⇒ℕ-preserves-⊇ (sucs n) (choice (d , i) cs) config =
  ⟦ choice (d , i) cs ⟧₂ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (config (d , i)) ⟧₂ config
  ≡˘⟨ Eq.cong₂ (⟦_⟧₂) {u = config} (Eq.cong₂ Vec.lookup {x = cs} refl (Eq.cong config (Eq.cong₂ _,_ refl (ℕ≥.cappedFin-toℕ i)))) refl ⟩
  ⟦ Vec.lookup cs (config (d , ℕ≥.cappedFin (Fin.toℕ i))) ⟧₂ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) ⟧₂ config
  ≡⟨ 2AryChoice-Fin⇒ℕ-preserves-⊇ (sucs n) (Vec.lookup cs (2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i))) config ⟩
  ⟦ 2AryChoice-Fin⇒ℕ (sucs n) (Vec.lookup cs (2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i))) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧₂ (Vec.lookup-map (2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) (2AryChoice-Fin⇒ℕ (sucs n)) cs) refl ⟩
  ⟦ Vec.lookup (Vec.map (2AryChoice-Fin⇒ℕ (sucs n)) cs) (2AryChoiceConfig-Fin⇒ℕ (sucs n) config (d , Fin.toℕ i)) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ (sucs n) config)
  ≡⟨⟩
  ⟦ choice (d , Fin.toℕ i) (Vec.map (2AryChoice-Fin⇒ℕ (sucs n)) cs) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ (sucs n) config)
  ≡⟨⟩
  ⟦ 2AryChoice-Fin⇒ℕ (sucs n) (choice (d , i) cs) ⟧₂ (2AryChoiceConfig-Fin⇒ℕ (sucs n) config)
  ∎

2AryChoice-Fin⇒ℕ-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : 2AryChoice (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A) → ⟦ 2AryChoice-Fin⇒ℕ n expr ⟧₂ ≅[ 2AryChoiceConfig-Fin⇒ℕ⁻¹ n ][ 2AryChoiceConfig-Fin⇒ℕ n ] ⟦ expr ⟧₂
2AryChoice-Fin⇒ℕ-preserves n expr = 2AryChoice-Fin⇒ℕ-preserves-⊆ n expr , 2AryChoice-Fin⇒ℕ-preserves-⊇ n expr


conf : {D : Set} → ℕ≥ 2 → CCCꟲ D → 2AryChoiceConfig (D × ℕ)
conf n = 2AryChoiceConfig-Fin⇒ℕ n ∘ NAryChoiceConfig→2AryChoiceConfig n ∘ CCCꟲ→NAryChoiceConfig n

fnoc : {D : Set} → ℕ≥ 2 → 2AryChoiceConfig (D × ℕ) → CCCꟲ D
fnoc n = CCCꟲ→NAryChoiceConfig⁻¹ n ∘ NAryChoiceConfig→2AryChoiceConfig⁻¹ n ∘ 2AryChoiceConfig-Fin⇒ℕ⁻¹ n

preserves : {D A : Set} → (expr : CCC D ∞ A) → ⟦ translate expr ⟧₂ ≅[ fnoc (maxChoiceLength expr) ][ conf (maxChoiceLength expr) ] ⟦ expr ⟧ₐ
preserves expr =
  ⟦ translate expr ⟧₂
  ≅[]⟨⟩
  ⟦ 2AryChoice-Fin⇒ℕ (maxChoiceLength expr) (NAryChoice→2AryChoice (maxChoiceLength expr) (CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr))) ⟧₂
  ≅[]⟨ 2AryChoice-Fin⇒ℕ-preserves (maxChoiceLength expr) (NAryChoice→2AryChoice (maxChoiceLength expr) (CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr))) ⟩
  ⟦ NAryChoice→2AryChoice (maxChoiceLength expr) (CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)) ⟧₂
  ≅[]⟨ NAryChoice→2AryChoice-preserves (maxChoiceLength expr) (CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr)) ⟩
  ⟦ CCC→NAryChoice (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr) ⟧ₙ
  ≅[]⟨ CCC→NAryChoice-preserves (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr) ⟩
  ⟦ expr ⟧ₐ
  ≅[]-∎
