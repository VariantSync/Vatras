{-|
This module renames dimensions in algebraic decision trees.

The idea of this translation is to apply a renaming function `f : D₁ → D₂` to
all elements of `D₁` in the datastructure `ADT V D₁` to obtain a new
datastructure `ADT V D₂`. To prove preservation of the semantics, we also
require a left inverse `f⁻¹ : D₂ → D₁` of `f` as a proof that `f` is injective.
This precondition is necessary because a non-injective rename would reduce the
number of possible variants.
-}

open import Framework.Definitions using (𝔸; 𝔽; 𝕍)

module Translation.Lang.ADT.Rename (V : 𝕍) where

open import Size using (Size; ∞)
open import Data.Bool using (if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Product using () renaming (_,_ to _and_)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Expressiveness V using (_≽_; expressiveness-from-compiler)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All
open ADT using (ADT; ADTL; leaf; _⟨_,_⟩)

ADT-map-config : ∀ {D₁ D₂ : 𝔽}
  → (D₂ → D₁)
  → ADT.Configuration D₁
  → ADT.Configuration D₂
ADT-map-config f config = config ∘ f

rename : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → ADT V D₁ A
  → ADT V D₂ A
rename f (leaf v) = leaf v
rename f (d ADT.⟨ l , r ⟩) = f d ⟨ rename f l , rename f r ⟩

preserves-⊆ : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (expr : ADT V D₁ A)
  → ADT.⟦ rename f expr ⟧ ⊆[ ADT-map-config f ] ADT.⟦ expr ⟧
preserves-⊆ f (leaf v) config = refl
preserves-⊆ f (d ⟨ l , r ⟩) config =
    ADT.⟦ rename f (d ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    ADT.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ config
  ≡⟨⟩
    (if config (f d) then ADT.⟦ rename f l ⟧ config else ADT.⟦ rename f r ⟧ config)
  ≡⟨ Eq.cong₂ (if config (f d) then_else_) (preserves-⊆ f l config) (preserves-⊆ f r config) ⟩
    (if config (f d) then ADT.⟦ l ⟧ (config ∘ f) else ADT.⟦ r ⟧ (config ∘ f))
  ≡⟨⟩
    ADT.⟦ d ⟨ l , r ⟩ ⟧ (config ∘ f)
  ∎

preserves-⊇ : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (expr : ADT V D₁ A)
  → ADT.⟦ expr ⟧ ⊆[ ADT-map-config f⁻¹ ] ADT.⟦ rename f expr ⟧
preserves-⊇ f f⁻¹ is-inverse (leaf v) config = refl
preserves-⊇ f f⁻¹ is-inverse (d ⟨ l , r ⟩) config =
    ADT.⟦ d ⟨ l , r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then ADT.⟦ l ⟧ config else ADT.⟦ r ⟧ config)
  ≡⟨ Eq.cong₂ (if config d then_else_) (preserves-⊇ f f⁻¹ is-inverse l config) (preserves-⊇ f f⁻¹ is-inverse r config) ⟩
    (if config d then ADT.⟦ rename f l ⟧ (config ∘ f⁻¹) else ADT.⟦ rename f r ⟧ (config ∘ f⁻¹))
  ≡⟨ Eq.cong-app (Eq.cong-app (Eq.cong if_then_else_ (Eq.cong config (is-inverse d))) (ADT.⟦ rename f l ⟧ (config ∘ f⁻¹))) (ADT.⟦ rename f r ⟧ (config ∘ f⁻¹)) ⟨
    (if config (f⁻¹ (f d)) then ADT.⟦ rename f l ⟧ (config ∘ f⁻¹) else ADT.⟦ rename f r ⟧ (config ∘ f⁻¹))
  ≡⟨⟩
    ADT.⟦ f d ⟨ rename f l , rename f r ⟩ ⟧ (config ∘ f⁻¹)
  ≡⟨⟩
    ADT.⟦ rename f (d ⟨ l , r ⟩) ⟧ (config ∘ f⁻¹)
  ∎

preserves : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → (e : ADT V D₁ A)
  → ADT.⟦ rename f e ⟧ ≅[ ADT-map-config f ][ ADT-map-config f⁻¹ ] ADT.⟦ e ⟧
preserves f f⁻¹ is-inverse expr = preserves-⊆ f expr and preserves-⊇ f f⁻¹ is-inverse expr

ADT-rename : ∀ {D₁ D₂ : 𝔽}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (ADTL V D₁) (ADTL V D₂)
ADT-rename f f⁻¹ is-inverse .LanguageCompiler.compile = rename f
ADT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = ADT-map-config f⁻¹
ADT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = ADT-map-config f
ADT-rename f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)

ADT-rename≽ADT : ∀ {D₁ D₂ : Set}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → ADTL V D₂ ≽ ADTL V D₁
ADT-rename≽ADT f f⁻¹ is-inverse = expressiveness-from-compiler (ADT-rename f f⁻¹ is-inverse)
