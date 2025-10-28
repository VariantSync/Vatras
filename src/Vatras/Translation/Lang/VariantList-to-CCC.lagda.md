# Encoding Lists of Variants in Core Choice Calculus

## Module

```agda
open import Vatras.Framework.Definitions
open import Vatras.Data.EqIndexedSet

module Vatras.Translation.Lang.VariantList-to-CCC
  (Dimension : 𝔽)
  (𝔻 : Dimension)
  where
```

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.List.NonEmpty.Properties using () renaming (map-id to map⁺-id; map-∘ to map⁺-∘; map-cong to map⁺-cong)
open import Data.Product using (_,_; proj₁)

open import Function using (id; flip; _∘_; _$_)
open import Size

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Variants using (Rose; Variant-is-VL; encode-idemp)
open import Vatras.Lang.All.Fixed Dimension (Rose ∞)
open VariantList using (VariantList; VariantListL)
open CCC using (CCC; CCCL; _⟨_⟩)

open import Vatras.Util.List using (find-or-last; map-find-or-last)
```

## Translation

```agda
module Translate
  (embed : LanguageCompiler (Variant-is-VL (Rose ∞)) CCCL)
  where
  open LanguageCompiler embed using (compile; preserves) renaming (conf to v-conf)

  translate : ∀ {A} → VariantList A → CCC ∞ A
  translate vs =  𝔻 ⟨ map⁺ compile vs ⟩

  conf : VariantList.Configuration → CCC.Configuration
  conf cₗ _ = cₗ

  fnoc : CCC.Configuration → VariantList.Configuration
  fnoc c = c 𝔻
```

### Properties

```agda
  module Preservation (A : 𝔸) where
    ⟦_⟧ᵥ = Semantics (Variant-is-VL (Rose ∞))
    open import Data.Unit using (tt)

    -- The proofs for preserves-⊆ and preserves-⊇ are highly similar and contain copy-and-paste. I could not yet see though how to properly abstract to reuse.
    preserves-⊆ : ∀ (l : VariantList A)
      → VariantList.⟦ l ⟧ ⊆[ conf ] CCC.⟦ translate l ⟧
    preserves-⊆ (v ∷ []) n
      rewrite encode-idemp (Rose ∞) A embed (λ _ → n) v
      = refl
    preserves-⊆ (v ∷ w ∷ zs) zero
      rewrite encode-idemp (Rose ∞) A embed (λ _ → zero) v
      = refl
    preserves-⊆ (v ∷ w ∷ zs) (suc n) =
      begin
        VariantList.⟦ v ∷ w ∷ zs ⟧ (suc n)
      ≡⟨⟩
        VariantList.⟦ w ∷ zs ⟧ n
      ≡⟨⟩
        find-or-last n (w ∷ zs)
      ≡⟨ Eq.cong (find-or-last n) (
        begin
          w ∷ zs
        ≡⟨ map⁺-id (w ∷ zs) ⟨
          map⁺ id (w ∷ zs)
        ≡⟨ map⁺-cong (encode-idemp (Rose ∞) A embed c) (w ∷ zs) ⟨
          map⁺ (⟦⟧c ∘ compile) (w ∷ zs)
        ≡⟨ map⁺-∘ (w ∷ zs) ⟩
          map⁺ ⟦⟧c tail-in-ccc
        ∎)⟩
        find-or-last n (map⁺ ⟦⟧c tail-in-ccc)
      ≡⟨ map-find-or-last ⟦⟧c n tail-in-ccc ⟨
        ⟦⟧c (find-or-last n tail-in-ccc)
      ≡⟨⟩
        CCC.⟦ find-or-last n (compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        CCC.⟦ find-or-last (suc n) (compile v ∷ compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        CCC.⟦ find-or-last (c 𝔻)  (compile v ∷ compile w ∷ map compile zs) ⟧ c
      ≡⟨⟩
        CCC.⟦ 𝔻 ⟨ map⁺ compile (v ∷ w ∷ zs) ⟩ ⟧ c
      ∎
      where
        c = λ _ → suc n
        ⟦⟧c = flip CCC.⟦_⟧ c
        tail-in-ccc = compile w ∷ map compile zs

    preserves-⊇ : ∀ (l : VariantList A)
      → CCC.⟦ translate l ⟧ ⊆[ fnoc ] VariantList.⟦ l ⟧
    preserves-⊇ (v ∷ []) c -- This proof is the same as for the preserves-⊆ (so look there if you want to see a step by step proof)
      rewrite encode-idemp (Rose ∞) A embed c v
      = refl
    preserves-⊇ (v ∷ w ∷ zs) c with c 𝔻
    ... | zero = encode-idemp (Rose ∞) A embed c v
    ... | suc i =
      let ⟦⟧c = flip CCC.⟦_⟧ c
          tail = w ∷ zs
          tail-in-ccc = map⁺ compile tail
      in sym $
      begin
        find-or-last i tail
      ≡⟨ Eq.cong (find-or-last i) (sym (map⁺-id tail)) ⟩
        find-or-last i (map⁺ id tail)
      ≡⟨ Eq.cong (find-or-last i) (map⁺-cong (encode-idemp (Rose ∞) A embed c) tail) ⟨
        find-or-last i (map⁺ (⟦⟧c ∘ compile) tail)
      ≡⟨ Eq.cong (find-or-last i) (map⁺-∘ tail) ⟩
        find-or-last i (map⁺ ⟦⟧c tail-in-ccc)
      ≡⟨ sym (map-find-or-last ⟦⟧c i tail-in-ccc) ⟩
        ⟦⟧c (find-or-last i tail-in-ccc)
      ≡⟨⟩
        CCC.⟦_⟧ (find-or-last i tail-in-ccc) c
      ≡⟨⟩
        CCC.⟦ find-or-last i tail-in-ccc ⟧ c
      ∎

  VariantList→CCC : LanguageCompiler VariantListL CCCL
  VariantList→CCC = record
    { compile = translate
    ; config-compiler = λ _ → record { to = conf ; from = fnoc }
    ; preserves = λ {A} e →
      let open Preservation A in
        preserves-⊆ e , preserves-⊇ e
    }

  open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (_≽_)

  CCC≽VariantList : CCCL ≽ VariantListL
  CCC≽VariantList {A} e = translate e , ≅[]→≅ (LanguageCompiler.preserves VariantList→CCC e)
```
