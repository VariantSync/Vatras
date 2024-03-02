{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.BCC-to-FCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

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

open import Lang.FCC renaming (Configuration to FCCꟲ)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Lang.BCC renaming (Configuration to BCCꟲ)
module BCCModule {D} = Lang.BCC D
open BCCModule using (_-<_>-; _⟨_,_⟩)
module BCCSem {A} = Lang.BCC.Sem A Variant Artifact∈ₛVariant
open BCCSem using () renaming (⟦_⟧ to ⟦_⟧₂)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


translate : {i : Size} → {D A : Set} → BCC D i A → FCC (sucs zero) D i A
translate (a -< cs >-) = a -< List.map translate cs >-
translate (d ⟨ l , r ⟩) = d ⟨ translate l ∷ translate r ∷ [] ⟩

conf : {D : Set} → BCCꟲ D → FCCꟲ (sucs zero) D
conf config d with config d
... | true = zero
... | false = suc zero

fnoc : {D : Set} → FCCꟲ (sucs zero) D → BCCꟲ D
fnoc config d with config d
... | zero = true
... | suc zero = false

preserves-⊆ : {i : Size} → {D A : Set} → (expr : BCC D i A) → ⟦ translate expr ⟧ₙ ⊆[ fnoc ] ⟦ expr ⟧₂
preserves-⊆ (a -< cs >-) config =
  ⟦ translate (a -< cs >-) ⟧ₙ config
  ≡⟨⟩
  ⟦ a -< List.map translate cs >- ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (List.map translate cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ translate e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ (fnoc config)) cs)
  ≡⟨⟩
  ⟦ a -< cs >- ⟧₂ (fnoc config)
  ∎
preserves-⊆ (d ⟨ l , r ⟩) config =
  ⟦ translate (d ⟨ l , r ⟩) ⟧ₙ config
  ≡⟨⟩
  ⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (translate l ∷ translate r ∷ []) (config d) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-map (config d) translate (l ∷ r ∷ [])) refl ⟩
  ⟦ translate (Vec.lookup (l ∷ r ∷ []) (config d)) ⟧ₙ config
  ≡⟨ preserves-⊆ (Vec.lookup (l ∷ r ∷ []) (config d)) config ⟩
  ⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧₂ (fnoc config)
  ≡⟨ Eq.cong₂ ⟦_⟧₂ lemma refl ⟩
  ⟦ if (fnoc config d) then l else r ⟧₂ (fnoc config)
  ≡⟨⟩
  ⟦ d ⟨ l , r ⟩ ⟧₂ (fnoc config)
  ∎
  where
  lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if fnoc config d then a else b)
  lemma with config d
  ... | zero = refl
  ... | suc zero = refl

preserves-⊇ : {i : Size} → {D A : Set} → (expr : BCC D i A) → ⟦ expr ⟧₂ ⊆[ conf ] ⟦ translate expr ⟧ₙ
preserves-⊇ (a -< cs >-) config =
  ⟦ a -< cs >- ⟧₂ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧₂ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ translate e ⟧ₙ (conf config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (conf config)) (List.map translate cs))
  ≡⟨⟩
  ⟦ a -< List.map translate cs >- ⟧ₙ (conf config)
  ≡⟨⟩
  ⟦ translate (a -< cs >-) ⟧ₙ (conf config)
  ∎
preserves-⊇ (d ⟨ l , r ⟩) config =
  ⟦ d ⟨ l , r ⟩ ⟧₂ config
  ≡⟨⟩
  ⟦ if config d then l else r ⟧₂ config
  ≡⟨⟩
  ⟦ if config d then l else r ⟧₂ config
  ≡⟨ preserves-⊇ (if config d then l else r) config ⟩
  ⟦ translate (if config d then l else r) ⟧ₙ (conf config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (push-function-into-if (translate) (config d)) refl ⟩
  ⟦ if config d then translate l else translate r ⟧ₙ (conf config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ lemma refl ⟩
  ⟦ Vec.lookup (translate l ∷ translate r ∷ []) (conf config d) ⟧ₙ (conf config)
  ≡⟨⟩
  ⟦ d ⟨ translate l ∷ translate r ∷ [] ⟩ ⟧ₙ (conf config)
  ≡⟨⟩
  ⟦ translate (d ⟨ l , r ⟩) ⟧ₙ (conf config)
  ∎
  where
  lemma : {A : Set} → {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (conf config d)
  lemma with config d
  ... | true = refl
  ... | false = refl

preserves : {i : Size} → {D A : Set} → (e : BCC D i A) → ⟦ translate e ⟧ₙ ≅[ fnoc ][ conf ] ⟦ e ⟧₂
preserves expr = preserves-⊆ expr and preserves-⊇ expr