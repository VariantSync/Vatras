{-# OPTIONS --sized-types #-}

module Translation.Lang.BCC-to-BCC where

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
open import Util.AuxProofs as ℕ using (if-cong)
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.Choices
open import Lang.BCC using (BCC; _-<_>-; _⟨_,_⟩)
module BCCSem {A} = Lang.BCC.Sem A Variant Artifact∈ₛVariant
open BCCSem using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Construct.Artifact as Artifact using () renaming (Syntax to Artifact)
import Construct.Choices as Chc
module Choice₂ = Chc.Choice₂
open Choice₂ using () renaming (Syntax to Choice₂)


map-dim : {i : Size} → {D₁ D₂ A : Set} → (D₁ → D₂) → BCC D₁ i A → BCC D₂ i A
map-dim f (a -< cs >-) = a -< List.map (map-dim f) cs >-
map-dim f (d ⟨ l , r ⟩) = f d ⟨ map-dim f l , map-dim f r ⟩

preserves-⊆ : {i : Size} → {D₁ D₂ A : Set} → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → (expr : BCC D₁ i A) → ⟦ map-dim f expr ⟧₂ ⊆[ _∘ f ] ⟦ expr ⟧₂
preserves-⊆ f f⁻¹ (a -< cs >-) config =
  ⟦ map-dim f (a -< cs >-) ⟧₂ config
  ≡⟨⟩
  ⟦ a -< List.map (map-dim f) cs >- ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map (map-dim f) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ map-dim f e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ f f⁻¹ e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ (config ∘ f)) cs)
  ≡⟨⟩
  ⟦ a -< cs >- ⟧₂ (config ∘ f)
  ∎
preserves-⊆ f f⁻¹ (d ⟨ l , r ⟩) config =
  ⟦ map-dim f (d ⟨ l , r ⟩) ⟧₂ config
  ≡⟨⟩
  ⟦ f d ⟨ map-dim f l , map-dim f r ⟩ ⟧₂ config
  ≡⟨⟩
  ⟦ if config (f d) then map-dim f l else map-dim f r ⟧₂ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧₂ (push-function-into-if (map-dim f) (config (f d))) refl ⟩
  ⟦ map-dim f (if config (f d) then l else r) ⟧₂ config
  ≡⟨ preserves-⊆ f f⁻¹ (if config (f d) then l else r) config ⟩
  ⟦ if config (f d) then l else r ⟧₂ (config ∘ f)
  ≡⟨⟩
  ⟦ if config (f d) then l else r ⟧₂ (config ∘ f)
  ≡⟨⟩
  ⟦ d ⟨ l , r ⟩ ⟧₂ (config ∘ f)
  ∎

preserves-⊇ : {i : Size} → {D₁ D₂ A : Set} → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → (expr : BCC D₁ i A) → ⟦ expr ⟧₂ ⊆[ _∘ f⁻¹ ] ⟦ map-dim f expr ⟧₂
preserves-⊇ f f⁻¹ is-inverse (a -< cs >-) config =
  ⟦ a -< cs >- ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ f f⁻¹ is-inverse e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ map-dim f e ⟧₂ (config ∘ f⁻¹)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ (config ∘ f⁻¹)) (List.map (map-dim f) cs))
  ≡⟨⟩
  ⟦ a -< List.map (map-dim f) cs >- ⟧₂ (config ∘ f⁻¹)
  ≡⟨⟩
  ⟦ map-dim f (a -< cs >-) ⟧₂ (config ∘ f⁻¹)
  ∎
preserves-⊇ f f⁻¹ is-inverse (d ⟨ l , r ⟩) config =
  ⟦ d ⟨ l , r ⟩ ⟧₂ config
  ≡⟨⟩
  ⟦ if config d then l else r ⟧₂ config
  ≡⟨⟩
  ⟦ if config d then l else r ⟧₂ config
  ≡⟨ preserves-⊇ f f⁻¹ is-inverse (if config d then l else r) config ⟩
  ⟦ map-dim f (if config d then l else r) ⟧₂ (config ∘ f⁻¹)
  ≡⟨ Eq.cong₂ ⟦_⟧₂ (push-function-into-if (map-dim f) (config d)) refl ⟩
  ⟦ if config d then map-dim f l else map-dim f r ⟧₂ (config ∘ f⁻¹)
  ≡˘⟨ Eq.cong₂ ⟦_⟧₂ (Eq.cong-app (Eq.cong-app (Eq.cong if_then_else_ (Eq.cong config (is-inverse d))) (map-dim f l)) (map-dim f r)) refl ⟩
  ⟦ if config (f⁻¹ (f d)) then map-dim f l else map-dim f r ⟧₂ (config ∘ f⁻¹)
  ≡⟨⟩
  ⟦ f d ⟨ map-dim f l , map-dim f r ⟩ ⟧₂ (config ∘ f⁻¹)
  ≡⟨⟩
  ⟦ map-dim f (d ⟨ l , r ⟩) ⟧₂ (config ∘ f⁻¹)
  ∎

preserves : {i : Size} → {D₁ D₂ A : Set} → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → (e : BCC D₁ i A) → ⟦ map-dim f e ⟧₂ ≅[ _∘ f ][ _∘ f⁻¹ ] ⟦ e ⟧₂
preserves f f⁻¹ is-inverse expr = preserves-⊆ f f⁻¹ expr and preserves-⊇ f f⁻¹ is-inverse expr
