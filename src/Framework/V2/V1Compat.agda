-- This file exists just for temporary compatibility clone-and-own with the old framework.
-- This file should be removed once all changes are reintegrated back to the original framework.
module Framework.V2.V1Compat where

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
import Data.IndexedSet

open import Framework.V2.Definitions
open import Framework.V2.Variants

private
  variable
    A : 𝔸

Complete : ∀ {V F S} → VariabilityLanguage V F S → Set₁
Complete {V} (L with-sem ⟦_⟧) = ∀ {A n}
  → (vs : VMap V A n)
    ----------------------------------
  → Σ[ e ∈ L A ]
      (let open Data.IndexedSet (VariantSetoid V A) renaming (_≅_ to _≋_)
        in vs ≋ ⟦ e ⟧)

record TranslationResult {V F S₁ S₂} (L₁ : VariabilityLanguage V F S₁) (L₂ : VariabilityLanguage V F S₂) : Set₁ where
  field
    expr : Expression L₂ A
    conf : Config F S₁ → Config F S₂
    fnoc : Config F S₂ → Config F S₁
open TranslationResult public

Translation : ∀ {V F S₁ S₂} (L₁ : VariabilityLanguage V F S₁) (L₂ : VariabilityLanguage V F S₂) → Set₁
Translation L₁ L₂ = ∀ {A : 𝔸} → Expression L₁ A → TranslationResult L₁ L₂

open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)
open import Level using (0ℓ)

EXPR : ∀ (V : 𝕍) (F : 𝔽) (S : 𝕊) (A : 𝔸) → VariabilityLanguage V F S → Set
EXPR _ _ _ A L = Expression L A
-- EXPR : ∀ {V F S} (A : 𝔸) → VariabilityLanguage V F S → Set
-- EXPR A L = Expression L A

-- _⊆ᵥ_ : ∀ {V F S A} → IRel (EXPR V F S A) 0ℓ
_⊆ᵥ_ : ∀ {V F S} {Γ₁ : VariabilityLanguage V F S} {Γ₂ : VariabilityLanguage V F S} {A}
  → Expression Γ₁ A
  → Expression Γ₂ A
  → Set
_⊆ᵥ_ {V} {_} {_} {L₁} {L₂} {A} e₁ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
  where ⟦_⟧₁ = Semantics L₁
        ⟦_⟧₂ = Semantics L₂
        open Data.IndexedSet (VariantSetoid V A) using (_⊆_)
infix 5 _⊆ᵥ_

-- _≚_ : ∀ {A : 𝔸} → IRel (Expression A) 0ℓ
_,_⊢_≚_ : ∀ {V F₁ F₂ S₁ S₂ A}
  → (Γ₁ : VariabilityLanguage V F₁ S₁)
  → (Γ₂ : VariabilityLanguage V F₂ S₂)
  → Expression Γ₁ A
  → Expression Γ₂ A
  → Set
_,_⊢_≚_ {V} {_} {_} {_} {_} {A} L₁ L₂ e₁ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
  where ⟦_⟧₁ = Semantics L₁
        ⟦_⟧₂ = Semantics L₂
        open Data.IndexedSet (VariantSetoid V A) using (_≅_)
infix 5 _,_⊢_≚_

Conf-Preserves :  ∀ {V F S₁ S₂}
  → (L₁ : VariabilityLanguage V F S₁)
  → (L₂ : VariabilityLanguage V F S₂)
  → Expression L₁ A
  → Expression L₂ A
  → (Config F S₁ → Config F S₂)
  → Set
Conf-Preserves {F = F} {S₁ = S₁} L₁ L₂ e₁ e₂ conf =
  ∀ (c₁ : Config F S₁) → ⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₂ ⟧₂ (conf c₁)
  where ⟦_⟧₁ = Semantics L₁
        ⟦_⟧₂ = Semantics L₂

Fnoc-Preserves :  ∀ {V F S₁ S₂}
  → (L₁ : VariabilityLanguage V F S₁)
  → (L₂ : VariabilityLanguage V F S₂)
  → Expression L₁ A
  → Expression L₂ A
  → (Config F S₂ → Config F S₁)
  → Set
Fnoc-Preserves {F = F} {S₂ = S₂} L₁ L₂ e₁ e₂ fnoc =
  ∀ (c₂ : Config F S₂) → ⟦ e₂ ⟧₂ c₂ ≡ ⟦ e₁ ⟧₁ (fnoc c₂)
  where ⟦_⟧₁ = Semantics L₁
        ⟦_⟧₂ = Semantics L₂

_⊆ₛ-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : Expression L₁ A)
  → Translation L₁ L₂
  → Set
_⊆ₛ-via_ {L₁ = L₁} {L₂ = L₂} e₁ translate = Conf-Preserves L₁ L₂ e₁ (expr (translate e₁)) (conf (translate e₁))

_⊇-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : Expression L₁ A)
  → Translation L₁ L₂
  → Set
_⊇-via_ {L₁ = L₁} {L₂ = L₂} e₁ translate = Fnoc-Preserves L₁ L₂ e₁ (expr (translate e₁)) (fnoc (translate e₁))

_≚-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : Expression L₁ A)
  → Translation L₁ L₂
  → Set
e ≚-via t = e ⊆ₛ-via t × e ⊇-via t

_is-variant-preserving :  ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂} → Translation L₁ L₂ → Set₁
_is-variant-preserving {L₁ = L₁} t = ∀ {A : 𝔸} → (e₁ : Expression L₁ A) → e₁ ≚-via t

-- -- any language with artifacts and choices is complete
-- choices-make-complete : ∀ {V F S}
--   → (VL : VariabilityLanguage V F S)
--   → (let L = Expression VL in
--       Artifact L ∈ₛ L
--     → Choice F L ∈ₛ L
--     → Complete VL)
-- -- TODO: Reuse the proof that variant lists are complete. Then show that
-- --       every language with at least artifacts and choices is at least
-- --       as expressive as a variant list.
-- choices-make-complete VL mkArtifact mkChoice vs = {!!}


