{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.NCC-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Size using (Size; ∞)
open import Util.List using (find-or-last; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

import Lang.CCC
module CCC where
  open Lang.CCC public
  module CCC-Sem-1 D = Lang.CCC.Sem D Variant Artifact∈ₛVariant
  open CCC-Sem-1 using (CCCL) public
  module CCC-Sem-2 {D} = Lang.CCC.Sem D Variant Artifact∈ₛVariant
  open CCC-Sem-2 using (⟦_⟧) public
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)

import Lang.NCC
module NCC where
  open Lang.NCC public
  module NCC-Sem-1 n D = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-1 using (NCCL) public
  module NCC-Sem-2 {n} {D} = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-2 using (⟦_⟧) public
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

artifact : ∀ {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


translate : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → NCC n D i A
  → CCC D ∞ A
translate n (a -< cs >-) = a -< List.map (translate n) cs >-
translate (sucs n) (d ⟨ c ∷ cs ⟩) = d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩

conf : ∀ {D : Set}
  → (n : ℕ≥ 2)
  → NCC.Configuration n D
  → CCC.Configuration D
conf (sucs n) config d = Fin.toℕ (config d)

fnoc : ∀ {D : Set}
  → (n : ℕ≥ 2)
  → CCC.Configuration D
  → NCC.Configuration n D
fnoc (sucs n) config d = ℕ≥.cappedFin (config d)


preserves-⊆ : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → CCC.⟦ translate n expr ⟧ ⊆[ fnoc n ] NCC.⟦ expr ⟧
preserves-⊆ n (a -< cs >-) config =
    CCC.⟦ translate n (a -< cs >-) ⟧ config
  ≡⟨⟩
    CCC.⟦ a -< List.map (translate n) cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → CCC.⟦ e ⟧ config) (List.map (translate n) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → CCC.⟦ e ⟧ config)} {f = translate n} cs) ⟩
    artifact a (List.map (λ e → CCC.⟦ translate n e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ n e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (fnoc n config)) cs)
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (fnoc n config)
  ∎
preserves-⊆ (sucs n) (d ⟨ c ∷ cs ⟩) config =
    CCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ config
  ≡⟨⟩
    CCC.⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ find-or-last (config d) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ config
  ≡˘⟨ Eq.cong₂ CCC.⟦_⟧ (lookup⇒find-or-last {m = config d} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟩
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (config d)) ⟧ config
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (Vec.lookup-map (ℕ≥.cappedFin (config d)) (translate (sucs n)) (c ∷ cs)) refl ⟩
    CCC.⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) ⟧ config
  ≡⟨ preserves-⊆ (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) config ⟩
    NCC.⟦ Vec.lookup (c ∷ cs) (fnoc (sucs n) config d) ⟧ (fnoc (sucs n) config)
  ≡⟨⟩
    NCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ (fnoc (sucs n) config)
  ∎

preserves-⊇ : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → NCC.⟦ expr ⟧ ⊆[ conf n ] CCC.⟦ translate n expr ⟧
preserves-⊇ n (a -< cs >-) config =
    NCC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ n e config) cs) ⟩
    artifact a (List.map (λ e → CCC.⟦ translate n e ⟧ (conf n config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ {g = (λ e → CCC.⟦ e ⟧ (conf n config))} {f = translate n} cs) ⟩
    artifact a (List.map (λ e → CCC.⟦ e ⟧ (conf n config)) (List.map (translate n) cs))
  ≡⟨⟩
    CCC.⟦ a -< List.map (translate n) cs >- ⟧ (conf n config)
  ≡⟨⟩
    CCC.⟦ translate n (a -< cs >-) ⟧ (conf n config)
  ∎
preserves-⊇ {D} {A} (sucs n) (d ⟨ c ∷ cs ⟩) config =
    NCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (c ∷ cs) (config d) ⟧ config
  ≡⟨ preserves-⊇ (sucs n) (Vec.lookup (c ∷ cs) (config d)) config ⟩
    CCC.⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (config d)) ⟧ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ CCC.⟦_⟧ (Vec.lookup-map (config d) (translate (sucs n)) (c ∷ cs)) refl ⟩
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (config d) ⟧ (conf (sucs n) config)
  ≡˘⟨ Eq.cong₂ CCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = Vec.map (translate (sucs n)) (c ∷ cs)}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (lookup⇒find-or-last {m = Fin.toℕ (config d)} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟩
    CCC.⟦ find-or-last (Fin.toℕ (config d)) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ (conf (sucs n) config)
  ≡⟨⟩
    CCC.⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ (conf (sucs n) config)
  ≡⟨⟩
    CCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ (conf (sucs n) config)
  ∎

preserves : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → CCC.⟦ translate n expr ⟧ ≅[ fnoc n ][ conf n ] NCC.⟦ expr ⟧
preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr

NCC→CCC : ∀ {i : Size} {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (NCCL n D {i}) (CCCL D)
NCC→CCC n .LanguageCompiler.compile = translate n
NCC→CCC n .LanguageCompiler.config-compiler expr .to = conf n
NCC→CCC n .LanguageCompiler.config-compiler expr .from = fnoc n
NCC→CCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)

CCC≽NCC : {D : Set} → (n : ℕ≥ 2) → CCCL D ≽ NCCL n D
CCC≽NCC n = expressiveness-from-compiler (NCC→CCC n)
