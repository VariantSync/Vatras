{-# OPTIONS --sized-types #-}

open import Framework.Definitions using (𝕍)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module renames dimensions in n-ary choice calculus expressions.
-}
module Translation.Lang.NCC.Rename (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ∞)
import Util.AuxProofs as ℕ
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

import Lang.NCC
module NCC where
  open Lang.NCC public
  module NCC-Sem-1 n D = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-1 using (NCCL) public
  module NCC-Sem-2 {n} {D} = Lang.NCC.Sem n D Variant Artifact∈ₛVariant
  open NCC-Sem-2 using (⟦_⟧) public
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

artifact : {A : 𝔸} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)

NCC-map-config : ∀ {D₁ D₂ : Set}
  → (n : ℕ≥ 2)
  → (D₂ → D₁)
  → NCC.Configuration n D₁
  → NCC.Configuration n D₂
NCC-map-config n f config = config ∘ f

rename : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (D₁ → D₂)
  → NCC n D₁ i A
  → NCC n D₂ i A
rename n f (a -< cs >-) = a -< List.map (rename n f) cs >-
rename n f (d ⟨ cs ⟩) = f d ⟨ Vec.map (rename n f) cs ⟩

preserves-⊆ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → (expr : NCC n D₁ i A)
  → NCC.⟦ rename n f expr ⟧ ⊆[ NCC-map-config n f ] NCC.⟦ expr ⟧
preserves-⊆ n f f⁻¹ (a -< cs >-) config =
    NCC.⟦ rename n f (a -< cs >-) ⟧ config
  ≡⟨⟩
    NCC.⟦ a -< List.map (rename n f) cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) (List.map (rename n f) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ rename n f e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ n f f⁻¹ e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (config ∘ f)) cs)
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (config ∘ f)
  ∎
preserves-⊆ n f f⁻¹ (d ⟨ cs ⟩) config =
    NCC.⟦ rename n f (d ⟨ cs ⟩) ⟧ config
  ≡⟨⟩
    NCC.⟦ f d ⟨ Vec.map (rename n f) cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (Vec.map (rename n f) cs) (config (f d)) ⟧ config
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config (f d)) (rename n f) cs) refl ⟩
    NCC.⟦ rename n f (Vec.lookup cs (config (f d))) ⟧ config
  ≡⟨ preserves-⊆ n f f⁻¹ (Vec.lookup cs (config (f d))) config ⟩
    NCC.⟦ Vec.lookup cs (config (f d)) ⟧ (config ∘ f)
  ≡⟨⟩
    NCC.⟦ d ⟨ cs ⟩ ⟧ (config ∘ f)
  ∎

preserves-⊇ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (expr : NCC n D₁ i A)
  → NCC.⟦ expr ⟧ ⊆[ NCC-map-config n f⁻¹ ] NCC.⟦ rename n f expr ⟧
preserves-⊇ n f f⁻¹ is-inverse (a -< cs >-) config =
    NCC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ n f f⁻¹ is-inverse e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ rename n f e ⟧ (config ∘ f⁻¹)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (config ∘ f⁻¹)) (List.map (rename n f) cs))
  ≡⟨⟩
    NCC.⟦ a -< List.map (rename n f) cs >- ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    NCC.⟦ rename n f (a -< cs >-) ⟧ (config ∘ f⁻¹)
  ∎
preserves-⊇ n f f⁻¹ is-inverse (d ⟨ cs ⟩) config =
    NCC.⟦ d ⟨ cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup cs (config d) ⟧ config
  ≡⟨ preserves-⊇ n f f⁻¹ is-inverse (Vec.lookup cs (config d)) config ⟩
    NCC.⟦ rename n f (Vec.lookup cs (config d)) ⟧ (config ∘ f⁻¹)
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config d) (rename n f) cs) refl ⟩
    NCC.⟦ Vec.lookup (Vec.map (rename n f) cs) (config d) ⟧ (config ∘ f⁻¹)
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = Vec.map (rename n f) cs} refl (Eq.cong config (is-inverse d))) refl ⟩
    NCC.⟦ Vec.lookup (Vec.map (rename n f) cs) (config ((f⁻¹ ∘ f) d)) ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    NCC.⟦ f d ⟨ Vec.map (rename n f) cs ⟩ ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    NCC.⟦ rename n f (d ⟨ cs ⟩) ⟧ (config ∘ f⁻¹)
  ∎

preserves : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (e : NCC n D₁ i A)
  → NCC.⟦ rename n f e ⟧ ≅[ NCC-map-config n f ][ NCC-map-config n f⁻¹ ] NCC.⟦ e ⟧
preserves n f f⁻¹ is-inverse expr = preserves-⊆ n f f⁻¹ expr , preserves-⊇ n f f⁻¹ is-inverse expr

NCC-rename : ∀ {i : Size} {D₁ D₂ : Set}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (NCCL n D₁ {i}) (NCCL n D₂ {i})
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.compile = rename n f
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = NCC-map-config n f⁻¹
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = NCC-map-config n f
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves n f f⁻¹ is-inverse expr)
