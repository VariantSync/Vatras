{-|
This module renames dimensions in binary choice calculus expressions.

The idea of this translation is to apply a renaming function `f : D₁ → D₂` to
all elements of `D₁` in the datastructure `2CC D₁` to obtain a new datastructure
`2CC D₂`. To prove preservation of the semantics, we also require a left inverse
`f⁻¹ : D₂ → D₁` of `f` as a proof that `f` is injective. This precondition is
necessary because a non-injective rename would reduce the number of possible
variants.
-}
module Vatras.Translation.Lang.2CC.Rename where

open import Size using (Size; ∞)
open import Data.Bool using (if_then_else_)
import Data.Bool.Properties as Bool
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Product using () renaming (_,_ to _and_)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (_≽_; expressiveness-from-compiler)
open import Vatras.Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Vatras.Lang.All
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩)

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
  → (expr : 2CC D₁ i A)
  → 2CC.⟦ rename f expr ⟧ ⊆[ 2CC-map-config f ] 2CC.⟦ expr ⟧
preserves-⊆ f (a -< cs >-) config =
    2CC.⟦ rename f (a -< cs >-) ⟧ config
  ≡⟨⟩
    2CC.⟦ a -< List.map (rename f) cs >- ⟧ config
  ≡⟨⟩
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ config) (List.map (rename f) cs) >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → 2CC.⟦ rename f e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊆ f e config) cs) ⟩
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ (config ∘ f)) cs >-
  ≡⟨⟩
    2CC.⟦ a -< cs >- ⟧ (config ∘ f)
  ∎
preserves-⊆ f (d ⟨ l , r ⟩) config =
    2CC.⟦ rename f (d ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    2CC.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ config
  ≡⟨⟩
    (if config (f d) then 2CC.⟦ rename f l ⟧ config else 2CC.⟦ rename f r ⟧ config)
  ≡⟨ Bool.if-cong₂ _ (preserves-⊆ f l config) (preserves-⊆ f r config) ⟩
    (if config (f d) then 2CC.⟦ l ⟧ (config ∘ f) else 2CC.⟦ r ⟧ (config ∘ f))
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
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊇ f f⁻¹ is-inverse e config) cs) ⟩
    a V.-< List.map (λ e → 2CC.⟦ rename f e ⟧ (config ∘ f⁻¹)) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟩
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ (config ∘ f⁻¹)) (List.map (rename f) cs) >-
  ≡⟨⟩
    2CC.⟦ a -< List.map (rename f) cs >- ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    2CC.⟦ rename f (a -< cs >-) ⟧ (config ∘ f⁻¹)
  ∎
preserves-⊇ f f⁻¹ is-inverse (d ⟨ l , r ⟩) config =
    2CC.⟦ d ⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then 2CC.⟦ l ⟧ config else 2CC.⟦ r ⟧ config)
  ≡⟨ Bool.if-cong₂ _ (preserves-⊇ f f⁻¹ is-inverse l config) (preserves-⊇ f f⁻¹ is-inverse r config) ⟩
    (if config d then 2CC.⟦ rename f l ⟧ (config ∘ f⁻¹) else 2CC.⟦ rename f r ⟧ (config ∘ f⁻¹))
  ≡⟨ Bool.if-cong (Eq.cong config (Eq.sym (is-inverse d))) ⟩
    (if (config ∘ f⁻¹) (f d) then 2CC.⟦ rename f l ⟧ (config ∘ f⁻¹) else 2CC.⟦ rename f r ⟧ (config ∘ f⁻¹))
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
preserves f f⁻¹ is-inverse expr = preserves-⊆ f expr and preserves-⊇ f f⁻¹ is-inverse expr

2CC-rename : ∀ {i : Size} {D₁ D₂ : 𝔽}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (2CCL D₁ {i}) (2CCL D₂ {i})
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.compile = rename f
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = 2CC-map-config f⁻¹
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = 2CC-map-config f
2CC-rename f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)

2CC-rename≽2CC : ∀ {i : Size} {D₁ D₂ : Set}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → 2CCL D₂ {i} ≽ 2CCL D₁ {i}
2CC-rename≽2CC f f⁻¹ is-inverse = expressiveness-from-compiler (2CC-rename f f⁻¹ is-inverse)
