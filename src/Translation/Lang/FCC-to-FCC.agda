{-# OPTIONS --sized-types #-}
module Translation.Lang.FCC-to-FCC where

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

NAryChoice→increasedNAryChoice : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → NAryChoice n D A {i} → NAryChoice m D A
NAryChoice→increasedNAryChoice n m n≤m (artifact a cs) = artifact a (List.map (NAryChoice→increasedNAryChoice n m n≤m) cs)
NAryChoice→increasedNAryChoice (sucs n) m n≤m (choice d cs) = choice d (Vec.saturate n≤m (Vec.map (NAryChoice→increasedNAryChoice (sucs n) m n≤m) cs))


NAryChoiceConfig→increasedNAryChoiceConfig : {D : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → NAryChoiceConfig n D → NAryChoiceConfig m D
NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d = Fin.inject≤ (config d) n≤m

NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ : {D : Set} → (n m : ℕ≥ 2) → n ℕ≥.≤ m → NAryChoiceConfig m D → NAryChoiceConfig n D
NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs n) (sucs m) n≤m config d = ℕ≥.cappedFin (Fin.toℕ (config d))

NAryChoice→increasedNAryChoice-preserves-⊆ : ∀ {i : Size} {D A : Set} (n m : ℕ≥ 2)
  → (n≤m : n ℕ≥.≤ m)
  → (expr : NAryChoice n D A {i})
  → ⟦ NAryChoice→increasedNAryChoice n m n≤m expr ⟧ₙ ⊆[ NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ n m n≤m ] ⟦ expr ⟧ₙ
NAryChoice→increasedNAryChoice-preserves-⊆ n m n≤m (artifact a cs) config =
  ⟦ NAryChoice→increasedNAryChoice n m n≤m (artifact a cs) ⟧ₙ config
  ≡⟨⟩
  ⟦ artifact a (List.map (NAryChoice→increasedNAryChoice n m n≤m) cs) ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map (NAryChoice→increasedNAryChoice n m n≤m) cs))
  ≡˘⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice→increasedNAryChoice n m n≤m e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → NAryChoice→increasedNAryChoice-preserves-⊆ n m n≤m e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ n m n≤m config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ n m n≤m config)
  ∎
NAryChoice→increasedNAryChoice-preserves-⊆ (sucs n) (sucs m) n≤m (choice d cs) config =
  ⟦ NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m (choice d cs) ⟧ₙ config
  ≡⟨⟩
  ⟦ choice d (Vec.saturate n≤m (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs)) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs)) (config d) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
  ⟦ Vec.lookup (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (config d) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config d) (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
  ⟦ (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (config d)) ⟧ₙ config
  ≡⟨ NAryChoice→increasedNAryChoice-preserves-⊆ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (config d)) config ⟩
  ⟦ Vec.lookup (Vec.saturate n≤m cs) (config d) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs n) (sucs m) n≤m config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate n≤m cs (config d)) refl ⟩
  ⟦ Vec.lookup cs (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs n) (sucs m) n≤m config d) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
  ⟦ choice d cs ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs n) (sucs m) n≤m config)
  ∎

NAryChoice→increasedNAryChoice-preserves-⊇ : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → (n≤m : n ℕ≥.≤ m) → (expr : NAryChoice n D A {i}) → ⟦ expr ⟧ₙ ⊆[ NAryChoiceConfig→increasedNAryChoiceConfig n m n≤m ] ⟦ NAryChoice→increasedNAryChoice n m n≤m expr ⟧ₙ
NAryChoice→increasedNAryChoice-preserves-⊇ n m n≤m (artifact a cs) config =
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → NAryChoice→increasedNAryChoice-preserves-⊇ n m n≤m e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice→increasedNAryChoice n m n≤m e ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig n m n≤m config)) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
  ⟦ artifact a (List.map (NAryChoice→increasedNAryChoice n m n≤m) cs) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig n m n≤m config)
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig n m n≤m config)) (List.map (NAryChoice→increasedNAryChoice n m n≤m) cs))
  ∎
NAryChoice→increasedNAryChoice-preserves-⊇ (sucs n) (sucs m) n≤m (choice d cs) config =
  ⟦ choice d cs ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (config d) ⟧ₙ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = cs}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
  ⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = cs}) (Eq.cong ℕ≥.cappedFin (Fin.toℕ-inject≤ (config d) n≤m))) refl ⟩
  ⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (Fin.inject≤ (config d) n≤m))) ⟧ₙ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate n≤m cs (Fin.inject≤ (config d) n≤m)) refl ⟩
  ⟦ Vec.lookup (Vec.saturate n≤m cs) (Fin.inject≤ (config d) n≤m) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.saturate n≤m cs) (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d) ⟧ₙ config
  ≡⟨ NAryChoice→increasedNAryChoice-preserves-⊇ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d)) config ⟩
  ⟦ (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d)) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d) (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
  ⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs)) (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config d) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
  ⟦ choice d (Vec.saturate n≤m (Vec.map (NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m) cs)) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
  ⟦ NAryChoice→increasedNAryChoice (sucs n) (sucs m) n≤m (choice d cs) ⟧ₙ (NAryChoiceConfig→increasedNAryChoiceConfig (sucs n) (sucs m) n≤m config)
  ∎

NAryChoice→increasedNAryChoice-preserves : {D A : Set} → (n m : ℕ≥ 2) → (n≤m : n ℕ≥.≤ m) → (expr : NAryChoice n D A) → ⟦ NAryChoice→increasedNAryChoice n m n≤m expr ⟧ₙ ≅[ NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ n m n≤m ][ NAryChoiceConfig→increasedNAryChoiceConfig n m n≤m ] ⟦ expr ⟧ₙ
NAryChoice→increasedNAryChoice-preserves n m n≤m expr = NAryChoice→increasedNAryChoice-preserves-⊆ n m n≤m expr , NAryChoice→increasedNAryChoice-preserves-⊇ n m n≤m expr


NAryChoice→2AryChoice : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → NAryChoice n D A {i} → 2AryChoice (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A
NAryChoice→2AryChoice n (artifact a cs) = artifact a (List.map (NAryChoice→2AryChoice n) cs)
NAryChoice→2AryChoice {i} {D} {A} (sucs n) (choice d cs) = go n (ℕ.n<1+n n) cs
  module NAryChoice→2AryChoice-Implementation where
  go : {i : Size} → (m : ℕ) → (m≤n : m < suc n) → Vec (NAryChoice (sucs n) D A {i}) (suc (suc m)) → 2AryChoice (D × Fin (suc n)) A
  go zero m≤n (l ∷ r ∷ []) = choice (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ [])
  go (suc m) m≤n (c ∷ cs) = choice (d , Fin.opposite (Fin.fromℕ< {suc m} m≤n)) (NAryChoice→2AryChoice (sucs n) c ∷ go m (<-trans (ℕ.n<1+n m) m≤n) cs ∷ [])


NAryChoiceConfig→2AryChoiceConfig : {D : Set} → (n : ℕ≥ 2) → NAryChoiceConfig n D → 2AryChoiceConfig (D × Fin (ℕ≥.toℕ (ℕ≥.pred n)))
NAryChoiceConfig→2AryChoiceConfig (sucs n) config (d , m) with config d Fin.≟ (Fin.inject₁ m)
... | yes _ = zero
... | no _ = suc zero

NAryChoiceConfig→2AryChoiceConfig⁻¹ : {D : Set} → (n : ℕ≥ 2) → 2AryChoiceConfig (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) → NAryChoiceConfig n D
NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d = go n (ℕ.n<1+n n)
  module NAryChoiceConfig→2AryChoiceConfig⁻¹-Implementation where
  go : (m : ℕ) → m < suc n → Fin (suc (suc n))
  go m m<n with config (d , Fin.opposite (Fin.fromℕ< {m} m<n))
  go m m<n | zero = Fin.inject₁ (Fin.opposite (Fin.fromℕ< {m} m<n))
  go zero m<n | suc zero = Fin.fromℕ (suc n)
  go (suc m) m<n | suc zero = go m (<-trans (ℕ.n<1+n m) m<n)

-- TODO move out of top-level
config≡0 : {D : Set} → {d : D} → {n : ℕ} → (config : 2AryChoiceConfig (D × Fin (suc n))) → (j : Fin (suc n)) → NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d ≡ Fin.inject₁ j → config (d , j) ≡ zero
config≡0 {d = d} {n = n} config j config≡j = go' n (ℕ.n<1+n n) config≡j
  where
  open NAryChoiceConfig→2AryChoiceConfig⁻¹-Implementation

  go' : (m : ℕ) → (m<n : m < suc n) → go n config d m m<n ≡ Fin.inject₁ j → config (d , j) ≡ zero
  go' m m<n go≡j with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
  go' m m<n go≡j | zero = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl (Eq.sym (Fin.inject₁-injective go≡j)))) config-opposite-m
  go' zero m<n go≡j | suc zero = ⊥-elim (Fin.toℕ-inject₁-≢ j (Eq.trans (Eq.sym (Fin.toℕ-fromℕ (suc n))) (Eq.cong Fin.toℕ go≡j)))
  go' (suc m) m<n go≡j | suc zero = go' m (<-trans (ℕ.n<1+n m) m<n) go≡j

config≡1 : {D : Set} → {d : D} → {n : ℕ} → (config : 2AryChoiceConfig (D × Fin (suc n))) → (j : Fin (suc n)) → j Fin.< NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d → config (d , j) ≡ suc zero
config≡1 {d = d} {n = n} config j config<j = go' n (ℕ.n<1+n n) config<j (λ k<opposite-n → ⊥-elim (ℕ.n≮0 (≤-trans k<opposite-n (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (ℕ.n<1+n n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (ℕ.n<1+n n))) (ℕ.n∸n≡0 n)))))))
  where
  open NAryChoiceConfig→2AryChoiceConfig⁻¹-Implementation

  extend-∀config≡1
    : {m : ℕ}
    → (m<n : suc m < suc n)
    → config (d , Fin.opposite (Fin.fromℕ< {suc m} m<n)) ≡ suc zero
    → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {suc m}                    m<n ) → config (d , k) ≡ suc zero)
    → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {    m} (<-trans (ℕ.n<1+n m) m<n)) → config (d , k) ≡ suc zero)
  extend-∀config≡1 {m} m<n config≡1 ∀config≡1 {k} m<k with k Fin.≟ Fin.opposite (Fin.fromℕ< {suc m} m<n)
  ... | yes k≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl k≡m)) config≡1
  ... | no k≢m = ∀config≡1 (ℕ.≤∧≢⇒< (ℕ.≤-pred (≤-trans m<k (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (ℕ.+-∸-assoc 1 (ℕ.≤-pred m<n)) (Eq.cong suc (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n))))))))))) (k≢m ∘ Fin.toℕ-injective))

  go' : (m : ℕ) → (m<n : m < suc n) → j Fin.< go n config d m m<n → (∀ {k : Fin (suc n)} → k Fin.< Fin.opposite (Fin.fromℕ< {m} m<n) → config (d , k) ≡ suc zero) → config (d , j) ≡ suc zero
  go' m m<n j<go ∀config≡1 with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
  go' m m<n j<go ∀config≡1 | zero with Fin.opposite (Fin.fromℕ< {m} m<n) Fin.≤? j
  go' m m<n j<go ∀config≡1 | zero | yes m≤j = ⊥-elim (ℕ.n≮n (Fin.toℕ j) (≤-trans j<go (≤-trans (≤-reflexive (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m<n)))) m≤j)))
  go' m m<n j<go ∀config≡1 | zero | no m≰j = ∀config≡1 (ℕ.≰⇒> m≰j)
  go' m m<n j<go ∀config≡1 | suc zero with j Fin.≟ Fin.opposite (Fin.fromℕ< {m} m<n)
  go' m m<n j<go ∀config≡1 | suc zero | yes j≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl j≡m)) config-opposite-m
  go' zero m<n j<go ∀config≡1 | suc zero | no j≢m = ∀config≡1 (ℕ.≤∧≢⇒< (≤-trans (ℕ.≤-pred (Fin.toℕ<n j)) (≤-reflexive (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n)))))) (j≢m ∘ Fin.toℕ-injective))
  go' (suc m) m<n j<go ∀config≡1 | suc zero | no j≢m = go' m (<-trans (ℕ.n<1+n m) m<n) j<go (extend-∀config≡1 {m = m} m<n config-opposite-m ∀config≡1)

NAryChoice→2AryChoice-preserves-⊆ : {i : Size} {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A {i}) → ⟦ NAryChoice→2AryChoice n expr ⟧₂ ⊆[ NAryChoiceConfig→2AryChoiceConfig⁻¹ n ] ⟦ expr ⟧ₙ
NAryChoice→2AryChoice-preserves-⊆ (sucs n) (artifact a cs) config =
  ⟦ NAryChoice→2AryChoice (sucs n) (artifact a cs) ⟧₂ config
  ≡⟨⟩
  ⟦ artifact a (List.map (NAryChoice→2AryChoice (sucs n)) cs) ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map (NAryChoice→2AryChoice (sucs n)) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ NAryChoice→2AryChoice (sucs n) e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → NAryChoice→2AryChoice-preserves-⊆ (sucs n) e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
  ∎
NAryChoice→2AryChoice-preserves-⊆ {D = D} {A = A} (sucs n) (choice d cs) config =
  ⟦ NAryChoice→2AryChoice (sucs n) (choice d cs) ⟧₂ config
  ≡⟨ lemma n (ℕ.n<1+n n) cs (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d) (ℕ.+-comm n (Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d))) ⟩
  ⟦ Vec.lookup cs (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d) ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
  ≡⟨⟩
  ⟦ choice d cs ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
  ∎
  where
  open NAryChoice→2AryChoice-Implementation

  lemma
    : {i : Size}
    → (m : ℕ)
    → (m≤n : m < suc n)
    → (cs' : Vec (NAryChoice (sucs n) D A {i}) (suc (suc m)))
    → (j : Fin (suc (suc m)))
    → m + Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d) ≡ Fin.toℕ j + n
    → ⟦ go n d cs m m≤n cs' ⟧₂ config ≡ ⟦ Vec.lookup cs' j ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
  lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
    ⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧₂ config
    ≡⟨⟩
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) ⟧₂ config
    ≡⟨⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧₂ config
    ≡⟨ Eq.cong₂ ⟦_⟧₂ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []} refl (config≡0 config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (Eq.trans m+config-d≡j+n (Eq.trans (Eq.sym (Fin.toℕ-fromℕ n)) (Eq.trans (Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n)))) (Eq.sym (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))))))))) refl ⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) zero ⟧₂ config
    ≡⟨⟩
    ⟦ NAryChoice→2AryChoice (sucs n) l ⟧₂ config
    ≡⟨ NAryChoice→2AryChoice-preserves-⊆ (sucs n) l config ⟩
    ⟦ l ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
    ∎
  lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< m≤n)) (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) ⟧₂ config
    ≡⟨⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧₂ config
    ≡⟨ Eq.cong₂ ⟦_⟧₂ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []} refl (config≡1 config (Fin.opposite (Fin.fromℕ< m≤n))
      (let module ≤ = ℕ.≤-Reasoning in
        ≤.begin-strict
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
        ≤.≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
        n
        ≤.<⟨ ℕ.n<1+n n ⟩
        suc n
        ≤.≡˘⟨ m+config-d≡j+n ⟩
        Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d)
        ≤.∎
      ))) refl ⟩
    ⟦ NAryChoice→2AryChoice (sucs n) r ⟧₂ config
    ≡⟨ NAryChoice→2AryChoice-preserves-⊆ (sucs n) r config ⟩
    ⟦ r ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
    ∎
  lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< m≤n)) (NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []) ⟧₂ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (config≡0 config (Fin.opposite (Fin.fromℕ< {suc m} m≤n)) (Fin.toℕ-injective (
        Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d)) ⟩
        suc m + Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d) ∸ suc m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
        n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
        n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
    ⟦ NAryChoice→2AryChoice (sucs n) c ⟧ₙ config
    ≡⟨ NAryChoice→2AryChoice-preserves-⊆ (sucs n) c config ⟩
    ⟦ c ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
    ∎
  lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) (NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []) ⟧₂ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (config≡1 config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
      (let module ≤ = ℕ.≤-Reasoning in
        ≤.begin-strict
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≤.≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
        ≤.≡⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
        n ∸ suc m
        ≤.<⟨ ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))) ⟩
        Fin.toℕ j + (n ∸ m)
        ≤.≡˘⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
        Fin.toℕ j + n ∸ m
        ≤.≡⟨⟩
        suc (Fin.toℕ j + n) ∸ suc m
        ≤.≡˘⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
        suc m + Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d) ∸ suc m
        ≤.≡⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d)) ⟩
        Fin.toℕ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config d)
        ≤.∎
      ))) refl ⟩
    ⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧₂ config
    ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
    ⟦ Vec.lookup cs' j ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig⁻¹ (sucs n) config)
    ∎

NAryChoice→2AryChoice-preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A {i}) → ⟦ expr ⟧ₙ ⊆[ NAryChoiceConfig→2AryChoiceConfig n ] ⟦ NAryChoice→2AryChoice n expr ⟧₂
NAryChoice→2AryChoice-preserves-⊇ (sucs n) (artifact a cs) config =
  ⟦ artifact a cs ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → NAryChoice→2AryChoice-preserves-⊇ (sucs n) e config) cs) ⟩
  artifact a (List.map (λ z → ⟦ NAryChoice→2AryChoice (sucs n) z ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)) (List.map (NAryChoice→2AryChoice (sucs n)) cs))
  ≡⟨⟩
  ⟦ NAryChoice→2AryChoice (sucs n) (artifact a cs) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
  ∎
NAryChoice→2AryChoice-preserves-⊇ {D = D} {A = A} (sucs n) (choice d cs) config =
  ⟦ choice d cs ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup cs (config d) ⟧ₙ config
  ≡˘⟨ lemma n (ℕ.n<1+n n) cs (config d) (ℕ.+-comm n (Fin.toℕ (config d))) ⟩
  ⟦ NAryChoice→2AryChoice (sucs n) (choice d cs) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
  ∎
  where
  open NAryChoice→2AryChoice-Implementation

  config≡0' : {D : Set} → {d : D} → {n : ℕ} → (config : NAryChoiceConfig (sucs n) D) → (j : Fin (suc n)) → config d ≡ (Fin.inject₁ j) → NAryChoiceConfig→2AryChoiceConfig (sucs n) config (d , j) ≡ zero
  config≡0' {d = d} config j config-d≡j with config d Fin.≟ (Fin.inject₁ j)
  ... | yes _ = refl
  ... | no config-d≢j = ⊥-elim (config-d≢j config-d≡j)

  config≡1' : {D : Set} → {d : D} → {n : ℕ} → (config : NAryChoiceConfig (sucs n) D) → (j : Fin (suc n)) → config d ≢ (Fin.inject₁ j) → NAryChoiceConfig→2AryChoiceConfig (sucs n) config (d , j) ≡ suc zero
  config≡1' {d = d} config j config-d≢j with config d Fin.≟ (Fin.inject₁ j)
  ... | yes config-d≡j = ⊥-elim (config-d≢j config-d≡j)
  ... | no _ = refl

  lemma
    : {i : Size}
    → (m : ℕ)
    → (m≤n : m < suc n)
      → (cs' : Vec (NAryChoice (sucs n) D A {i}) (suc (suc m)))
    → (j : Fin (suc (suc m)))
    → m + Fin.toℕ (config d) ≡ Fin.toℕ j + n
    → ⟦ go n d cs m m≤n cs' ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config) ≡ ⟦ Vec.lookup cs' j ⟧ₙ config
  lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
    ⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨⟩
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) (NAryChoiceConfig→2AryChoiceConfig (sucs n) config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨ Eq.cong₂ ⟦_⟧₂ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []} refl (config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
        Fin.toℕ (config d)
        ≡⟨ m+config-d≡j+n ⟩
        n
        ≡˘⟨ Fin.toℕ-fromℕ n ⟩
        Fin.toℕ (Fin.fromℕ n)
        ≡⟨ Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n))) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) zero ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨⟩
    ⟦ NAryChoice→2AryChoice (sucs n) l ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡˘⟨ NAryChoice→2AryChoice-preserves-⊇ (sucs n) l config ⟩
    ⟦ l ⟧ₙ config
    ∎
  lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< m≤n)) (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨⟩
    ⟦ Vec.lookup (NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []) (NAryChoiceConfig→2AryChoiceConfig (sucs n) config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨ Eq.cong₂ ⟦_⟧₂ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) l ∷ NAryChoice→2AryChoice (sucs n) r ∷ []} refl (config≡1' config (Fin.opposite (Fin.fromℕ< m≤n)) (λ config-d≡opposite-m → ℕ.1+n≢n (
        suc n
        ≡˘⟨ m+config-d≡j+n ⟩
        Fin.toℕ (config d)
        ≡⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
        ≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
        n ∸ zero
        ≡⟨⟩
        n
        ∎
      )))) refl ⟩
    ⟦ NAryChoice→2AryChoice (sucs n) r ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡˘⟨ NAryChoice→2AryChoice-preserves-⊇ (sucs n) r config ⟩
    ⟦ r ⟧ₙ config
    ∎
  lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< m≤n)) (NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
        Fin.toℕ (config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
        suc m + Fin.toℕ (config d) ∸ suc m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
        n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
        n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
    ⟦ NAryChoice→2AryChoice (sucs n) c ⟧ₙ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡˘⟨ NAryChoice→2AryChoice-preserves-⊇ (sucs n) c config ⟩
    ⟦ c ⟧ₙ config
    ∎
  lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
    ⟦ choice (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) (NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []) ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup {x = NAryChoice→2AryChoice (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (config≡1' config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
      (λ config-d≡opposite-m → (ℕ.<⇒≢ (ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))))) (
        n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
        n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
        Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
        Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))) ⟩
        Fin.toℕ (Fin.inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))))
        ≡˘⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
        Fin.toℕ (config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
        suc m + Fin.toℕ (config d) ∸ suc m
        ≡⟨⟩
        m + Fin.toℕ (config d) ∸ m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
        Fin.toℕ j + n ∸ m
        ≡⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
        Fin.toℕ j + (n ∸ m)
        ∎
      )))) refl ⟩
    ⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧₂ (NAryChoiceConfig→2AryChoiceConfig (sucs n) config)
    ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
    ⟦ Vec.lookup cs' j ⟧ₙ config
    ∎

NAryChoice→2AryChoice-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : NAryChoice n D A) → ⟦ NAryChoice→2AryChoice n expr ⟧₂ ≅[ NAryChoiceConfig→2AryChoiceConfig⁻¹ n ][ NAryChoiceConfig→2AryChoiceConfig n ] ⟦ expr ⟧ₙ
NAryChoice→2AryChoice-preserves n expr = NAryChoice→2AryChoice-preserves-⊆ n expr , NAryChoice→2AryChoice-preserves-⊇ n expr


2AryChoice→NAryChoice : {D A : Set} → (n : ℕ≥ 2) → 2AryChoice D A → NAryChoice n D A
2AryChoice→NAryChoice (sucs n) = NAryChoice→increasedNAryChoice (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

2AryChoiceConfig→NAryChoiceConfig : {D : Set} → (n : ℕ≥ 2) → 2AryChoiceConfig D → NAryChoiceConfig n D
2AryChoiceConfig→NAryChoiceConfig (sucs n) = NAryChoiceConfig→increasedNAryChoiceConfig (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

2AryChoiceConfig→NAryChoiceConfig⁻¹ : {D : Set} → (n : ℕ≥ 2) → NAryChoiceConfig n D → 2AryChoiceConfig D
2AryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) = NAryChoiceConfig→increasedNAryChoiceConfig⁻¹ (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)

2AryChoice→NAryChoice-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : 2AryChoice D A) → ⟦ 2AryChoice→NAryChoice n expr ⟧ₙ ≅[ 2AryChoiceConfig→NAryChoiceConfig⁻¹ n ][ 2AryChoiceConfig→NAryChoiceConfig n ] ⟦ expr ⟧₂
2AryChoice→NAryChoice-preserves (sucs n) = NAryChoice→increasedNAryChoice-preserves (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)


NAryChoice→NAryChoice : {i : Size} → {D A : Set} → (n m : ℕ≥ 2) → NAryChoice n D A {i} → NAryChoice m (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))) A
NAryChoice→NAryChoice (sucs n) (sucs m) expr = 2AryChoice→NAryChoice (sucs m) (NAryChoice→2AryChoice (sucs n) expr)

NAryChoice→NAryChoice-preserves : {D A : Set} → (n m : ℕ≥ 2) → (expr : NAryChoice n D A) → ⟦ NAryChoice→NAryChoice n m expr ⟧ₙ ≅[ NAryChoiceConfig→2AryChoiceConfig⁻¹ n ∘ 2AryChoiceConfig→NAryChoiceConfig⁻¹ m ][ 2AryChoiceConfig→NAryChoiceConfig m ∘ NAryChoiceConfig→2AryChoiceConfig n ] ⟦ expr ⟧ₙ
NAryChoice→NAryChoice-preserves (sucs n) (sucs m) expr = ≅[]-trans (2AryChoice→NAryChoice-preserves (sucs m) (NAryChoice→2AryChoice (sucs n) expr)) (NAryChoice→2AryChoice-preserves (sucs n) expr)
