# Encoding Lists of Variants in Core Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact)

module Translation.Lang.VariantList-to-CCC
  (Dimension : 𝔽)
  (𝔻 : Dimension)
  (V : 𝕍)
  (mkArtifact : Artifact ∈ₛ V)
  where
```

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.List.NonEmpty.Properties using () renaming (map-∘ to map⁺-∘; map-cong to map⁺-cong)
open import Data.Product using (_,_; proj₁)

open import Function using (id; flip; _∘_; _$_)
open import Size

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Framework.Compiler using (LanguageCompiler)
open import Lang.VariantList V as VL
  using (VariantList; VariantListL; VariantList-is-Complete)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Cₗ)
open import Lang.CCC Dimension as CCC-Module
  renaming (Configuration to Cᶜ)
open CCC-Module.Sem V mkArtifact
  -- using (CCC; CCCL; Artifact; _⟨_⟩; ⟦_⟧; compile; compile-preserves)

import Framework.Variant
open import Framework.Variants
open import Framework.FunctionLanguage as FL

open import Util.List using (find-or-last; map-find-or-last; map⁺-id)
```

## Translation

```agda
module Translate
  (embed : LanguageCompiler (Variant-is-VL V) CCCL)
  where
  open LanguageCompiler embed using (compile; preserves) renaming (conf to v-conf)

  translate : ∀ {A} → VariantList A ⇒ CCC ∞ A
  translate vs =  𝔻 ⟨ map⁺ compile vs ⟩

  conf : Cₗ ⇒ Cᶜ
  conf cₗ _ = cₗ

  fnoc : Cᶜ ⇒ Cₗ
  fnoc c = c 𝔻
```

### Properties

```agda
  module Preservation (A : 𝔸) where
    open Framework.Variant V A
    open import Framework.Variability.Completeness V using (Complete)
    open import Data.IndexedSet VariantSetoid using (_≅_; irrelevant-index; _⊆[_]_; _≅[_][_]_; ≅[]→≅)

    ⟦_⟧ᵥ = Semantics (Variant-is-VL V)
    open import Data.Unit using (tt)

    -- The proofs for preserves-⊆ and preserves-⊇ are highly similar and contain copy-and-paste. I could not yet see though how to properly abstract to reuse.
    preserves-⊆ : ∀ (l : VariantList A)
      → ⟦ l ⟧ₗ ⊆[ conf ] ⟦ translate l ⟧
    preserves-⊆ (v ∷ []) n
      rewrite encode-idemp V A embed (λ _ → n) v
      = refl
    preserves-⊆ (v ∷ w ∷ zs) zero
      rewrite encode-idemp V A embed (λ _ → zero) v
      = refl
    preserves-⊆ (v ∷ w ∷ zs) (suc n) =
      begin
        ⟦ v ∷ w ∷ zs ⟧ₗ (suc n)
      ≡⟨⟩
        ⟦ w ∷ zs ⟧ₗ n
      ≡⟨⟩
        find-or-last n (w ∷ zs)
      ≡⟨ Eq.cong (find-or-last n) (
        begin
          w ∷ zs
        ≡˘⟨ map⁺-id (w ∷ zs) ⟩
          map⁺ id (w ∷ zs)
        ≡˘⟨ map⁺-cong (encode-idemp V A embed c) (w ∷ zs) ⟩
          map⁺ (⟦⟧c ∘ compile) (w ∷ zs)
        ≡⟨ map⁺-∘ (w ∷ zs) ⟩
          map⁺ ⟦⟧c tail-in-ccc
        ∎)⟩
        find-or-last n (map⁺ ⟦⟧c tail-in-ccc)
      ≡˘⟨ map-find-or-last ⟦⟧c n tail-in-ccc ⟩
        ⟦⟧c (find-or-last n tail-in-ccc)
      ≡⟨⟩
        ⟦ find-or-last n (compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        ⟦ find-or-last (suc n) (compile v ∷ compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        ⟦ find-or-last (c 𝔻)  (compile v ∷ compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        ⟦ 𝔻 ⟨ map⁺ compile (v ∷ w ∷ zs) ⟩ ⟧ c
      ∎
      where
        c = λ _ → suc n
        ⟦⟧c = flip ⟦_⟧ c
        tail-in-ccc = compile w ∷ map compile zs

    preserves-⊇ : ∀ (l : VariantList A)
      → ⟦ translate l ⟧ ⊆[ fnoc ] ⟦ l ⟧ₗ
    preserves-⊇ (v ∷ []) c -- This proof is the same as for the preserves-⊆ (so look there if you want to see a step by step proof)
      rewrite encode-idemp V A embed c v
      = refl
    preserves-⊇ (v ∷ w ∷ zs) c with c 𝔻
    ... | zero = encode-idemp V A embed c v
    ... | suc i =
      let ⟦⟧c = flip ⟦_⟧ c
          tail = w ∷ zs
          tail-in-ccc = map⁺ compile tail
      in Eq.sym $
      begin
        find-or-last i tail
      ≡⟨ Eq.cong (find-or-last i) (Eq.sym (map⁺-id tail)) ⟩
        find-or-last i (map⁺ id tail)
      ≡˘⟨ Eq.cong (find-or-last i) (map⁺-cong (encode-idemp V A embed c) tail) ⟩
        find-or-last i (map⁺ (⟦⟧c ∘ compile) tail)
      ≡⟨ Eq.cong (find-or-last i) (map⁺-∘ tail) ⟩
        find-or-last i (map⁺ ⟦⟧c tail-in-ccc)
      ≡⟨ Eq.sym (map-find-or-last ⟦⟧c i tail-in-ccc) ⟩
        ⟦⟧c (find-or-last i tail-in-ccc)
      ≡⟨⟩
        ⟦_⟧ (find-or-last i tail-in-ccc) c
      ≡⟨⟩
        ⟦ find-or-last i tail-in-ccc ⟧ c
      ∎

  VariantList→CCC : LanguageCompiler VariantListL CCCL
  VariantList→CCC = record
    { compile = translate
    ; config-compiler = record { to = conf ; from = fnoc }
    ; preserves = λ {A} e →
      let open Preservation A in
        preserves-⊆ e , preserves-⊇ e
    }

  open Framework.Variant V
  open FL.Comp VariantSetoid
  open import Framework.Variability.Completeness V
  import Data.IndexedSet

  -- TODO: Relate Compilers and Expressiveness in their own module.
  CCCL-is-at-least-as-expressive-as-VariantListL : CCCL ≽ VariantListL
  CCCL-is-at-least-as-expressive-as-VariantListL {A} e = translate e , ≅[]→≅ (LanguageCompiler.preserves VariantList→CCC e)
    where
      open Data.IndexedSet (VariantSetoid A) using (≅[]→≅)

  CCCL-is-complete : Complete CCCL
  CCCL-is-complete = completeness-by-expressiveness VariantList-is-Complete CCCL-is-at-least-as-expressive-as-VariantListL
```

