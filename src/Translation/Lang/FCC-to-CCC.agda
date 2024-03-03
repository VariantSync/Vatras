{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.FCC-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

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
open import Framework.Compiler using (LanguageCompiler)
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

open import Lang.FCC renaming (Configuration to FCCꟲ)
open Lang.FCC.Sem using (FCCL)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


translate : {i : Size} → (n : ℕ≥ 2) -> {D A : Set} → FCC n D i A → CCC D ∞ A
translate n (a -< cs >-) = a -< List.map (translate n) cs >-
translate (sucs n) (d ⟨ c ∷ cs ⟩) = d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩

conf : {D : Set} → (n : ℕ≥ 2) → FCCꟲ n D → CCCꟲ D
conf (sucs n) config d = Fin.toℕ (config d)

fnoc : {D : Set} → (n : ℕ≥ 2) → CCCꟲ D → FCCꟲ n D
fnoc (sucs n) config d = ℕ≥.cappedFin (config d)


preserves-⊆ : ∀ {i : Size} {D A : Set} (n : ℕ≥ 2)
  → (expr : FCC n D i A)
  → ⟦ translate n expr ⟧ₐ ⊆[ fnoc n ] ⟦ expr ⟧ₙ
preserves-⊆ n (a -< cs >-) config =
  ⟦ translate n (a -< cs >-) ⟧ₐ config
  ≡⟨⟩
  ⟦ a -< List.map (translate n) cs >- ⟧ₐ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ config) (List.map (translate n) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ config)} {f = translate n} cs) ⟩
  artifact a (List.map (λ e → ⟦ translate n e ⟧ₐ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc n config)) cs)
  ≡⟨⟩
  ⟦ a -< cs >- ⟧ₙ (fnoc n config)
  ∎
preserves-⊆ (sucs n) (d ⟨ c ∷ cs ⟩) config =
  ⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ₐ config
  ≡⟨⟩
  ⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ₐ config
  ≡⟨⟩
  ⟦ find-or-last (config d) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ₐ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = config d} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (config d)) ⟧ₐ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (ℕ≥.cappedFin (config d)) (translate (sucs n)) (c ∷ cs)) refl ⟩
  ⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) ⟧ₐ config
  ≡⟨ preserves-⊆ (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) config ⟩
  ⟦ Vec.lookup (c ∷ cs) (fnoc (sucs n) config d) ⟧ₙ (fnoc (sucs n) config)
  ≡⟨⟩
  ⟦ d ⟨ c ∷ cs ⟩ ⟧ₙ (fnoc (sucs n) config)
  ∎

preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ expr ⟧ₙ ⊆[ conf n ] ⟦ translate n expr ⟧ₐ
preserves-⊇ n (a -< cs >-) config =
  ⟦ a -< cs >- ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ n e config) cs) ⟩
  artifact a (List.map (λ e → ⟦ translate n e ⟧ₐ (conf n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → ⟦ e ⟧ₐ (conf n config))} {f = translate n} cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ (conf n config)) (List.map (translate n) cs))
  ≡⟨⟩
  ⟦ a -< List.map (translate n) cs >- ⟧ₐ (conf n config)
  ≡⟨⟩
  ⟦ translate n (a -< cs >-) ⟧ₐ (conf n config)
  ∎
preserves-⊇ {D} {A} (sucs n) (d ⟨ c ∷ cs ⟩) config =
  ⟦ d ⟨ c ∷ cs ⟩ ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (c ∷ cs) (config d) ⟧ₙ config
  ≡⟨ preserves-⊇ (sucs n) (Vec.lookup (c ∷ cs) (config d)) config ⟩
  ⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (config d)) ⟧ₐ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Vec.lookup-map (config d) (translate (sucs n)) (c ∷ cs)) refl ⟩
  ⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (config d) ⟧ₐ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₐ (Eq.cong₂ Vec.lookup (refl {x = Vec.map (translate (sucs n)) (c ∷ cs)}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
  ⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₐ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₐ (lookup⇒find-or-last {m = Fin.toℕ (config d)} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟩
  ⟦ find-or-last (Fin.toℕ (config d)) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ₐ (conf (sucs n) config)
  ≡⟨⟩
  ⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ₐ (conf (sucs n) config)
  ≡⟨⟩
  ⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ₐ (conf (sucs n) config)
  ∎

preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : FCC n D i A) → ⟦ translate n expr ⟧ₐ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₙ
preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr

FCC→CCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (FCCL n D Variant Artifact∈ₛVariant {i}) (CCCL D Variant Artifact∈ₛVariant)
FCC→CCC n .LanguageCompiler.compile = translate n
FCC→CCC n .LanguageCompiler.config-compiler expr .to = conf n
FCC→CCC n .LanguageCompiler.config-compiler expr .from = fnoc n
FCC→CCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)

CCC≽FCC : {D : Set} → (n : ℕ≥ 2) → CCCL D Variant Artifact∈ₛVariant ≽ FCCL n D Variant Artifact∈ₛVariant
CCC≽FCC n = expressiveness-from-compiler (FCC→CCC n)
