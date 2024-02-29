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
open import Size using (Size; ↑_)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.Choices

NAryChoice→ArbitraryChoice : {i : Size} → {n : ℕ≥ 2} -> {D A : Set} → NAryChoice n D A {i} → ArbitraryChoice D A
NAryChoice→ArbitraryChoice (artifact a cs) = artifact a (List.map NAryChoice→ArbitraryChoice cs)
NAryChoice→ArbitraryChoice {n = sucs n} (choice d (c ∷ cs)) = choice d (List⁺.fromVec (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs)))


NAryChoiceConfig→ArbitraryChoiceConfig : {D : Set} → (n : ℕ≥ 2) → NAryChoiceConfig n D → ArbitraryChoiceConfig D
NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config d = Fin.toℕ (config d)

NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ : {D : Set} → (n : ℕ≥ 2) → ArbitraryChoiceConfig D → NAryChoiceConfig n D
NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ (sucs n) config d = ℕ≥.cappedFin (config d)

NAryChoice→ArbitraryChoice-preserves-⊆ : ∀ {i : Size} {D A : Set} (n : ℕ≥ 2)
  → (expr : NAryChoice n D A {i})
  → ⟦ NAryChoice→ArbitraryChoice expr ⟧ₐ ⊆[ NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ n ] ⟦ expr ⟧ₙ
NAryChoice→ArbitraryChoice-preserves-⊆ n (artifact a cs) config =
  ⟦ NAryChoice→ArbitraryChoice (artifact a cs) ⟧ₐ config
  ≡⟨⟩
  ⟦ artifact a (List.map NAryChoice→ArbitraryChoice cs) ⟧ₐ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ config) (List.map NAryChoice→ArbitraryChoice cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ config)} {f = NAryChoice→ArbitraryChoice} cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice→ArbitraryChoice e ⟧ₐ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → NAryChoice→ArbitraryChoice-preserves-⊆ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ n config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧ₙ (NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ n config)
  ∎
NAryChoice→ArbitraryChoice-preserves-⊆ (sucs n) (choice d (c ∷ cs)) config =
  ⟦ NAryChoice→ArbitraryChoice (choice d (c ∷ cs)) ⟧ₐ config
  ≡⟨⟩
  ⟦ choice d (List⁺.fromVec (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs))) ⟧ₐ config
  ≡⟨⟩
  ⟦ find-or-last (config d) (List⁺.fromVec (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs))) ⟧ₐ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = config d} (NAryChoice→ArbitraryChoice c ∷ Vec.map NAryChoice→ArbitraryChoice cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs)) (ℕ≥.cappedFin (config d)) ⟧ₐ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (ℕ≥.cappedFin (config d)) NAryChoice→ArbitraryChoice (c ∷ cs)) refl ⟩
  ⟦ NAryChoice→ArbitraryChoice (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) ⟧ₐ config
  ≡⟨ NAryChoice→ArbitraryChoice-preserves-⊆ (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) config ⟩
  ⟦ Vec.lookup (c ∷ cs) (NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ (sucs n) config d) ⟧ₙ (NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ (sucs n) config)
  ≡⟨⟩
  ⟦ choice d (c ∷ cs) ⟧ₙ (NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ (sucs n) config)
  ∎

NAryChoice→ArbitraryChoice-preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A {i}) → ⟦ expr ⟧ₙ ⊆[ NAryChoiceConfig→ArbitraryChoiceConfig n ] ⟦ NAryChoice→ArbitraryChoice expr ⟧ₐ
NAryChoice→ArbitraryChoice-preserves-⊇ n (artifact a cs) config =
  ⟦ artifact a cs ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → NAryChoice→ArbitraryChoice-preserves-⊇ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice→ArbitraryChoice e ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig n config))} {f = NAryChoice→ArbitraryChoice} cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig n config)) (List.map NAryChoice→ArbitraryChoice cs))
  ≡⟨⟩
  ⟦ artifact a (List.map NAryChoice→ArbitraryChoice cs) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig n config)
  ≡⟨⟩
  ⟦ NAryChoice→ArbitraryChoice (artifact a cs) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig n config)
  ∎
NAryChoice→ArbitraryChoice-preserves-⊇ {D} {A} (sucs n) (choice d (c ∷ cs)) config =
  ⟦ choice d (c ∷ cs) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (c ∷ cs) (config d) ⟧ₙ config
  ≡⟨ NAryChoice→ArbitraryChoice-preserves-⊇ (sucs n) (Vec.lookup (c ∷ cs) (config d)) config ⟩
  ⟦ NAryChoice→ArbitraryChoice (Vec.lookup (c ∷ cs) (config d)) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (config d) NAryChoice→ArbitraryChoice (c ∷ cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs)) (config d) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Eq.cong₂ Vec.lookup (refl {x = Vec.map NAryChoice→ArbitraryChoice (c ∷ cs)}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
  ⟦ Vec.lookup (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = Fin.toℕ (config d)} (NAryChoice→ArbitraryChoice c ∷ Vec.map NAryChoice→ArbitraryChoice cs)) refl ⟩
  ⟦ find-or-last (Fin.toℕ (config d)) (List⁺.fromVec (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs))) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ≡⟨⟩
  ⟦ choice d (List⁺.fromVec (Vec.map NAryChoice→ArbitraryChoice (c ∷ cs))) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ≡⟨⟩
  ⟦ NAryChoice→ArbitraryChoice (choice d (c ∷ cs)) ⟧ₐ (NAryChoiceConfig→ArbitraryChoiceConfig (sucs n) config)
  ∎

NAryChoice→ArbitraryChoice-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A) → ⟦ NAryChoice→ArbitraryChoice expr ⟧ₐ ≅[ NAryChoiceConfig→ArbitraryChoiceConfig⁻¹ n ][ NAryChoiceConfig→ArbitraryChoiceConfig n ] ⟦ expr ⟧ₙ
NAryChoice→ArbitraryChoice-preserves n expr = NAryChoice→ArbitraryChoice-preserves-⊆ n expr , NAryChoice→ArbitraryChoice-preserves-⊇ n expr
