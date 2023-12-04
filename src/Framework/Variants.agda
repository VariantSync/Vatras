{-# OPTIONS --sized-types #-}

module Framework.Variants where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (map)
open import Function using (id; _∘_; flip)
open import Size using (Size; ↑_; ∞)

open import Framework.Definitions using (𝕍; 𝔸)
open import Framework.V2.Constructs.Artifact as At using (_-<_>-; map-children; map-children-preserves) renaming (Syntax to Artifact; Construct to ArtifactC)
open import Framework.VariabilityLanguage

data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} (a : A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

data Rose : Size → 𝕍 where
  rose : ∀ {i} {A : 𝔸} → Artifact (Rose i) A → Rose (↑ i) A

rose-leaf : ∀ {A : 𝔸} → A → Rose ∞ A
rose-leaf {A} a = rose (At.leaf (Rose ∞ A) a)

-- Variants are also variability languages
Variant-is-VL : ∀ (V : 𝕍) → VariabilityLanguage V
Variant-is-VL V = Lang-⟪ V , ⊤ , (λ e c → e) ⟫

GrulerVL : VariabilityLanguage GrulerVariant
GrulerVL = Variant-is-VL GrulerVariant

RoseVL : VariabilityLanguage (Rose ∞)
RoseVL = Variant-is-VL (Rose ∞)

-- Variants can be encoded into other variability language.
-- The result is an expression which cannot be configured
-- (i.e., configurations don't matter because there is only
-- a single variant anyway).

open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler

VariantEncoder : ∀ (V : 𝕍) (Γ : VariabilityLanguage V) → Set₁
VariantEncoder V Γ = LanguageCompiler (Variant-is-VL V) Γ

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

module _ (V : 𝕍) (A : 𝔸) {Γ : VariabilityLanguage V} (encoder : VariantEncoder V Γ) where
  open import Framework.Variant V A
  open import Data.IndexedSet VariantSetoid

  private
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics (Variant-is-VL V)

  encoded-variant-is-singleton-set :
    ∀ (v : V A) → Singleton ⟦ compile encoder v ⟧
  encoded-variant-is-singleton-set v = v , λ c → proj₂ (preserves encoder v) c

  encode-idemp : ∀ (c : Config Γ) (v : V A)
    → ⟦ compile encoder v ⟧ c ≡ v
  encode-idemp c v =
    begin
      ⟦ compile encoder v ⟧ c
    ≡⟨ irrelevant-index (encoded-variant-is-singleton-set v) ⟩
      ⟦ compile encoder v ⟧ (conf encoder tt)
    ≡˘⟨ proj₁ (preserves encoder v) tt ⟩
      ⟦ v ⟧ᵥ tt
    ≡⟨⟩
      v
    ∎

open import Framework.Construct

rose-encoder :
  ∀ (Γ : VariabilityLanguage (Rose ∞))
  → ArtifactC ⟦∈⟧ₚ Γ
  → Config Γ
  → VariantEncoder (Rose ∞) Γ
rose-encoder Γ has c = record
  { compile = t
  ; config-compiler = record { to = confi; from = fnoci }
  ; preserves = p
  }
  where
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics (Variant-is-VL (Rose ∞))

    confi : ⊤ → Config Γ
    confi _ =  c

    fnoci : Config Γ → ⊤
    fnoci _ = tt

    module _ {A : 𝔸} where
      t : ∀ {i} → Rose i A → Expression Γ A
      t (rose x) = cons (C∈ₛΓ has) (map-children t x)

      open import Framework.Variant (Rose ∞) A using (VariantSetoid)
      open import Data.IndexedSet VariantSetoid

      h : ∀ (v : Rose ∞ A) (j : Config Γ) → ⟦ t v ⟧ j ≡ v
      h (rose (a -< cs >-)) j =
        begin
          ⟦ cons (C∈ₛΓ has) (map-children t (a -< cs >-)) ⟧ j
        ≡⟨ resistant has (map-children t (a -< cs >-)) j ⟩
          (cons (C∈ₛV has) ∘ pcong ArtifactC Γ (map-children t (a -< cs >-))) j
        ≡⟨⟩
          cons (C∈ₛV has) (pcong ArtifactC Γ (a -< map t cs >-) j)
        ≡⟨ {!!} ⟩
          cons (C∈ₛV has) (a -< cs >-)
        ≡⟨ foo ⟩
          rose (a -< cs >-)
        ∎
        where
          foo : cons (C∈ₛV has) (a -< cs >-) ≡ rose (a -< cs >-)
          foo with cons (C∈ₛV has) (a -< cs >-) in eq
          ... | rose (b -< bs >-) = {!!}


      p : ∀ (e : Rose ∞ A) → ⟦ e ⟧ᵥ ≅[ confi ][ fnoci ] ⟦ t e ⟧
      p e = irrelevant-index-≅ e (λ i → refl) (λ j → h e j) confi fnoci
