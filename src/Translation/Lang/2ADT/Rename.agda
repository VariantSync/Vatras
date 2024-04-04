{-# OPTIONS --sized-types #-}

open import Framework.Definitions using (𝕍)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module renames dimensions in algebraic decision trees.
-}
module Translation.Lang.2ADT.Rename (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Product using () renaming (_,_ to _and_)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Expressiveness Variant using (_≽_; expressiveness-from-compiler)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
open import Size using (Size)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open 2ADT using (2ADT; 2ADTL; leaf; _⟨_,_⟩)

artifact : ∀ {A : 𝔸} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)

2ADT-map-config : ∀ {D₁ D₂ : 𝔽}
  → (D₂ → D₁)
  → 2ADT.Configuration D₁
  → 2ADT.Configuration D₂
2ADT-map-config f config = config ∘ f

rename : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → 2ADT Variant D₁ A
  → 2ADT Variant D₂ A
rename f (leaf v) = leaf v
rename f (d 2ADT.⟨ l , r ⟩) = f d ⟨ rename f l , rename f r ⟩

preserves-⊆ : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → (expr : 2ADT Variant D₁ A)
  → 2ADT.⟦ rename f expr ⟧ ⊆[ 2ADT-map-config f ] 2ADT.⟦ expr ⟧
preserves-⊆ f f⁻¹ (leaf v) config = refl
preserves-⊆ f f⁻¹ (d ⟨ l , r ⟩) config =
    2ADT.⟦ rename f (d ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    2ADT.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ config
  ≡⟨⟩
    (if config (f d) then 2ADT.⟦ rename f l ⟧ config else 2ADT.⟦ rename f r ⟧ config)
  ≡⟨ Eq.cong₂ (if config (f d) then_else_) (preserves-⊆ f f⁻¹ l config) (preserves-⊆ f f⁻¹ r config) ⟩
    (if config (f d) then 2ADT.⟦ l ⟧ (config ∘ f) else 2ADT.⟦ r ⟧ (config ∘ f))
  ≡⟨⟩
    2ADT.⟦ d ⟨ l , r ⟩ ⟧ (config ∘ f)
  ∎

preserves-⊇ : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (expr : 2ADT Variant D₁ A)
  → 2ADT.⟦ expr ⟧ ⊆[ 2ADT-map-config f⁻¹ ] 2ADT.⟦ rename f expr ⟧
preserves-⊇ f f⁻¹ is-inverse (leaf v) config = refl
preserves-⊇ f f⁻¹ is-inverse (d ⟨ l , r ⟩) config =
    2ADT.⟦ d ⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then 2ADT.⟦ l ⟧ config else 2ADT.⟦ r ⟧ config)
  ≡⟨ Eq.cong₂ (if config d then_else_) (preserves-⊇ f f⁻¹ is-inverse l config) (preserves-⊇ f f⁻¹ is-inverse r config) ⟩
    (if config d then 2ADT.⟦ rename f l ⟧ (config ∘ f⁻¹) else 2ADT.⟦ rename f r ⟧ (config ∘ f⁻¹))
  ≡˘⟨ Eq.cong-app (Eq.cong-app (Eq.cong if_then_else_ (Eq.cong config (is-inverse d))) (2ADT.⟦ rename f l ⟧ (config ∘ f⁻¹))) (2ADT.⟦ rename f r ⟧ (config ∘ f⁻¹)) ⟩
    (if config (f⁻¹ (f d)) then 2ADT.⟦ rename f l ⟧ (config ∘ f⁻¹) else 2ADT.⟦ rename f r ⟧ (config ∘ f⁻¹))
  ≡⟨⟩
    2ADT.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    2ADT.⟦ rename f (d ⟨ l , r ⟩) ⟧ (config ∘ f⁻¹)
  ∎

preserves : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (e : 2ADT Variant D₁ A)
  → 2ADT.⟦ rename f e ⟧ ≅[ 2ADT-map-config f ][ 2ADT-map-config f⁻¹ ] 2ADT.⟦ e ⟧
preserves f f⁻¹ is-inverse expr = preserves-⊆ f f⁻¹ expr and preserves-⊇ f f⁻¹ is-inverse expr

2ADT-rename : ∀ {D₁ D₂ : 𝔽}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (2ADTL Variant D₁) (2ADTL Variant D₂)
2ADT-rename f f⁻¹ is-inverse .LanguageCompiler.compile = rename f
2ADT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = 2ADT-map-config f⁻¹
2ADT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = 2ADT-map-config f
2ADT-rename f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)

2ADT-rename≽2ADT : ∀ {D₁ D₂ : Set}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → 2ADTL Variant D₂ ≽ 2ADTL Variant D₁
2ADT-rename≽2ADT f f⁻¹ is-inverse = expressiveness-from-compiler (2ADT-rename f f⁻¹ is-inverse)
