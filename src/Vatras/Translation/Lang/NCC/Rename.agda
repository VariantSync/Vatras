{-|
This module renames dimensions in n-ary choice calculus expressions.

The idea of this translation is to apply a renaming function `f : D₁ → D₂` to
all elements of `D₁` in the datastructure `NCC n D₁` to obtain a new
datastructure `NCC n D₂`. To prove preservation of the semantics, we also
require a left inverse `f⁻¹ : D₂ → D₁` of `f` as a proof that `f` is injective.
This precondition is necessary because a non-injective rename would reduce the
number of possible variants.
-}
module Vatras.Translation.Lang.NCC.Rename where

open import Size using (Size; ∞)
open import Data.Empty using (⊥-elim)
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Vatras.Framework.Compiler using (LanguageCompiler; _⊕_)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (_≽_; expressiveness-from-compiler)
open import Vatras.Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
import Vatras.Util.AuxProofs as ℕ
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Vatras.Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Vatras.Lang.All
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

NCC-map-config : ∀ {D₁ D₂ : Set}
  → (n : ℕ≥ 2)
  → (D₂ → D₁)
  → NCC.Configuration D₁ n
  → NCC.Configuration D₂ n
NCC-map-config n f config = config ∘ f

rename : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (D₁ → D₂)
  → NCC D₁ n i A
  → NCC D₂ n i A
rename n f (a -< cs >-) = a -< List.map (rename n f) cs >-
rename n f (d ⟨ cs ⟩) = f d ⟨ Vec.map (rename n f) cs ⟩

preserves-⊆ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (expr : NCC D₁ n i A)
  → NCC.⟦ rename n f expr ⟧ ⊆[ NCC-map-config n f ] NCC.⟦ expr ⟧
preserves-⊆ n f (a -< cs >-) config =
    NCC.⟦ rename n f (a -< cs >-) ⟧ config
  ≡⟨⟩
    NCC.⟦ a -< List.map (rename n f) cs >- ⟧ config
  ≡⟨⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ config) (List.map (rename n f) cs) >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → NCC.⟦ rename n f e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊆ n f e config) cs) ⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ (config ∘ f)) cs >-
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (config ∘ f)
  ∎
preserves-⊆ n f (d ⟨ cs ⟩) config =
    NCC.⟦ rename n f (d ⟨ cs ⟩) ⟧ config
  ≡⟨⟩
    NCC.⟦ f d ⟨ Vec.map (rename n f) cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (Vec.map (rename n f) cs) (config (f d)) ⟧ config
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config (f d)) (rename n f) cs) refl ⟩
    NCC.⟦ rename n f (Vec.lookup cs (config (f d))) ⟧ config
  ≡⟨ preserves-⊆ n f (Vec.lookup cs (config (f d))) config ⟩
    NCC.⟦ Vec.lookup cs (config (f d)) ⟧ (config ∘ f)
  ≡⟨⟩
    NCC.⟦ d ⟨ cs ⟩ ⟧ (config ∘ f)
  ∎

preserves-⊇ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (expr : NCC D₁ n i A)
  → NCC.⟦ expr ⟧ ⊆[ NCC-map-config n f⁻¹ ] NCC.⟦ rename n f expr ⟧
preserves-⊇ n f f⁻¹ is-inverse (a -< cs >-) config =
    NCC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊇ n f f⁻¹ is-inverse e config) cs) ⟩
    a V.-< List.map (λ e → NCC.⟦ rename n f e ⟧ (config ∘ f⁻¹)) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ (config ∘ f⁻¹)) (List.map (rename n f) cs) >-
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
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config d) (rename n f) cs) refl ⟨
    NCC.⟦ Vec.lookup (Vec.map (rename n f) cs) (config d) ⟧ (config ∘ f⁻¹)
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = Vec.map (rename n f) cs} refl (Eq.cong config (is-inverse d))) refl ⟨
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
  → (e : NCC D₁ n i A)
  → NCC.⟦ rename n f e ⟧ ≅[ NCC-map-config n f ][ NCC-map-config n f⁻¹ ] NCC.⟦ e ⟧
preserves n f f⁻¹ is-inverse expr = preserves-⊆ n f expr , preserves-⊇ n f f⁻¹ is-inverse expr

NCC-rename : ∀ {i : Size} {D₁ D₂ : Set}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (NCCL D₁ n {i}) (NCCL D₂ n {i})
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.compile = rename n f
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = NCC-map-config n f⁻¹
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = NCC-map-config n f
NCC-rename n f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves n f f⁻¹ is-inverse expr)

NCC-rename≽NCC : ∀ {i : Size} {D₁ D₂ : Set}
  → (n : ℕ≥ 2)
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → NCCL D₂ n {i} ≽ NCCL D₁ n {i}
NCC-rename≽NCC n f f⁻¹ is-inverse = expressiveness-from-compiler (NCC-rename n f f⁻¹ is-inverse)
