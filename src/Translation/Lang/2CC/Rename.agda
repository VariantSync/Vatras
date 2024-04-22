open import Framework.Definitions using (𝕍; atoms)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module renames dimensions in binary choice calculus expressions.
-}
module Translation.Lang.2CC.Rename (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (if_then_else_)
import Data.Bool.Properties as Bool
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

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩)

artifact : ∀ {A : 𝔸} → atoms A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)

2CC-map-config : ∀ {D₁ D₂ : 𝔽}
  → (D₂ → D₁)
  → 2CC.Configuration D₁
  → 2CC.Configuration D₂
2CC-map-config f config = config ∘ f

rename : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → 2CC D₁ i A
  → 2CC D₂ i A
rename f (a -< cs >-) = a -< List.map (rename f) cs >-
rename f (d ⟨ l , r ⟩) = f d ⟨ rename f l , rename f r ⟩

preserves-⊆ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → (expr : 2CC D₁ i A)
  → 2CC.⟦ rename f expr ⟧ ⊆[ 2CC-map-config f ] 2CC.⟦ expr ⟧
preserves-⊆ f f⁻¹ (a -< cs >-) config =
    2CC.⟦ rename f (a -< cs >-) ⟧ config
  ≡⟨⟩
    2CC.⟦ a -< List.map (rename f) cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → 2CC.⟦ e ⟧ config) (List.map (rename f) cs))
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟨
    artifact a (List.map (λ e → 2CC.⟦ rename f e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ f f⁻¹ e config) cs) ⟩
    artifact a (List.map (λ e → 2CC.⟦ e ⟧ (config ∘ f)) cs)
  ≡⟨⟩
    2CC.⟦ a -< cs >- ⟧ (config ∘ f)
  ∎
preserves-⊆ f f⁻¹ (d ⟨ l , r ⟩) config =
    2CC.⟦ rename f (d ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    2CC.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ config
  ≡⟨⟩
    2CC.⟦ if config (f d) then rename f l else rename f r ⟧ config
  ≡⟨ Eq.cong₂ 2CC.⟦_⟧ (Bool.if-float (rename f) (config (f d))) refl ⟨
    2CC.⟦ rename f (if config (f d) then l else r) ⟧ config
  ≡⟨ preserves-⊆ f f⁻¹ (if config (f d) then l else r) config ⟩
    2CC.⟦ if config (f d) then l else r ⟧ (config ∘ f)
  ≡⟨⟩
    2CC.⟦ if config (f d) then l else r ⟧ (config ∘ f)
  ≡⟨⟩
    2CC.⟦ d ⟨ l , r ⟩ ⟧ (config ∘ f)
  ∎

preserves-⊇ : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (expr : 2CC D₁ i A)
  → 2CC.⟦ expr ⟧ ⊆[ 2CC-map-config f⁻¹ ] 2CC.⟦ rename f expr ⟧
preserves-⊇ f f⁻¹ is-inverse (a -< cs >-) config =
    2CC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → 2CC.⟦ e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ f f⁻¹ is-inverse e config) cs) ⟩
    artifact a (List.map (λ e → 2CC.⟦ rename f e ⟧ (config ∘ f⁻¹)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → 2CC.⟦ e ⟧ (config ∘ f⁻¹)) (List.map (rename f) cs))
  ≡⟨⟩
    2CC.⟦ a -< List.map (rename f) cs >- ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    2CC.⟦ rename f (a -< cs >-) ⟧ (config ∘ f⁻¹)
  ∎
preserves-⊇ f f⁻¹ is-inverse (d ⟨ l , r ⟩) config =
    2CC.⟦ d ⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    2CC.⟦ if config d then l else r ⟧ config
  ≡⟨ preserves-⊇ f f⁻¹ is-inverse (if config d then l else r) config ⟩
    2CC.⟦ rename f (if config d then l else r) ⟧ (config ∘ f⁻¹)
  ≡⟨ Eq.cong₂ 2CC.⟦_⟧ (Bool.if-float (rename f) (config d)) refl ⟩
    2CC.⟦ if config d then rename f l else rename f r ⟧ (config ∘ f⁻¹)
  ≡⟨ Eq.cong₂ 2CC.⟦_⟧ (Eq.cong-app (Eq.cong-app (Eq.cong if_then_else_ (Eq.cong config (is-inverse d))) (rename f l)) (rename f r)) refl ⟨
    2CC.⟦ if config (f⁻¹ (f d)) then rename f l else rename f r ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    2CC.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    2CC.⟦ rename f (d ⟨ l , r ⟩) ⟧ (config ∘ f⁻¹)
  ∎

preserves : ∀ {i : Size} {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (e : 2CC D₁ i A)
  → 2CC.⟦ rename f e ⟧ ≅[ 2CC-map-config f ][ 2CC-map-config f⁻¹ ] 2CC.⟦ e ⟧
preserves f f⁻¹ is-inverse expr = preserves-⊆ f f⁻¹ expr and preserves-⊇ f f⁻¹ is-inverse expr

2CC-rename : ∀ {i : Size} {D₁ D₂ : 𝔽}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (2CCL {i} D₁) (2CCL {i} D₂)
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.compile = rename f
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = 2CC-map-config f⁻¹
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = 2CC-map-config f
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)

2CC-rename≽2CC : ∀ {i : Size} {D₁ D₂ : Set}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → 2CCL {i} D₂ ≽ 2CCL {i} D₁
2CC-rename≽2CC f f⁻¹ is-inverse = expressiveness-from-compiler (2CC-rename f f⁻¹ is-inverse)
