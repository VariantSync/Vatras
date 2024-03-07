{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.BCC-to-BCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Product using () renaming (_,_ to _and_)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
open import Size using (Size)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.BCC using (BCC; _-<_>-; _⟨_,_⟩)
module BCC-Sem1 D = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC-Sem1 using (BCCL)
module BCC-Sem2 {D} = Lang.BCC.Sem D Variant Artifact∈ₛVariant
open BCC-Sem2 using () renaming (⟦_⟧ to ⟦_⟧₂)

artifact : {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


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
  ≡˘⟨ Eq.cong₂ ⟦_⟧₂ (Bool.push-function-into-if (map-dim f) (config (f d))) refl ⟩
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

BCC-map-dim : {i : Size} → {D₁ D₂ : Set} → (f : D₁ → D₂) → (f⁻¹ : D₂ → D₁) → f⁻¹ ∘ f ≗ id → LanguageCompiler (BCCL D₁ {i}) (BCCL D₂ {i})
BCC-map-dim f f⁻¹ is-inverse .LanguageCompiler.compile = map-dim f
BCC-map-dim f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = _∘ f⁻¹
BCC-map-dim f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = _∘ f
BCC-map-dim f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)
