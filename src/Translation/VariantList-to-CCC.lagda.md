# Encoding Lists of Variants in Core Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.VariantList-to-CCC where
```

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; map)
open import Data.List.NonEmpty using (List⁺; _∷_) renaming (map to map⁺)
open import Data.List.NonEmpty.Properties using () renaming (map-∘ to map⁺-∘; map-cong to map⁺-cong)
open import Data.Product using (_,_)

open import Function using (id; flip; _∘_)
open import Size

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Definitions
open import Lang.Annotation.Name using (Dimension)
open import Lang.VariantList
  using (VariantList; VariantListL; VariantList-is-Complete)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Cₗ)
open import Lang.CCC
  using (CCC; CCCL; Artifact; _⟨_⟩; ⟦_⟧; describe-variant; describe-variant-preserves)
  renaming (Configuration to Cᶜ)

open import Translation.Translation using (Translation; TranslationResult; expr; conf; fnoc; _is-variant-preserving; expressiveness-by-translation)
open import Relations.Semantic using (_is-at-least-as-expressive-as_)
open import Lang.Properties.Completeness using (Complete)
open import Lang.Properties.Conclude.Completeness using (completeness-by-expressiveness)

open import Util.List using (find-or-last; map-find-or-last; map⁺-id)
```

## Translation

```agda
𝔻 : Dimension
𝔻 = "D"

VariantList→CCC : Translation VariantListL CCCL
VariantList→CCC vlist =
  record
  { expr = 𝔻 ⟨ map⁺ describe-variant vlist ⟩
  ; conf = λ cₗ _ → cₗ
  ; fnoc = λ c → c 𝔻
  }
```

### Properties

```agda

-- The proofs for preserves-⊆ and preserves-⊇ are highly similar and contain copy-and-paste. I could not yet see though how to properly abstract to reuse.
preserves-⊆ : ∀ {A} (l : VariantList ∞ A) (c : Cₗ) → ⟦ l ⟧ₗ c ≡ ⟦ expr (VariantList→CCC l) ⟧ (conf (VariantList→CCC l) c)
preserves-⊆ (v ∷ []) n =
  let c = λ _ → n
  in
  begin
    ⟦ v ∷ [] ⟧ₗ n
  ≡⟨ describe-variant-preserves v ⟩
    ⟦ describe-variant v ⟧ c
  ≡⟨⟩
    ⟦ find-or-last (c 𝔻) (describe-variant v ∷ []) ⟧ c
  ≡⟨⟩
    ⟦ 𝔻 ⟨ map⁺ describe-variant (v ∷ []) ⟩ ⟧ c
  ∎
preserves-⊆ (v ∷ w ∷ zs) zero = describe-variant-preserves v
preserves-⊆ (v ∷ w ∷ zs) (suc n) =
  let c = λ _ → suc n
      ⟦⟧c = flip ⟦_⟧ c
      tail-in-ccc = describe-variant w ∷ map describe-variant zs
  in
  begin
    ⟦ v ∷ w ∷ zs ⟧ₗ (suc n)
  ≡⟨⟩
    ⟦ w ∷ zs ⟧ₗ n
  ≡⟨⟩
    find-or-last n (w ∷ zs)
  ≡⟨ Eq.cong (find-or-last n) (Eq.sym (map⁺-id (w ∷ zs))) ⟩
    find-or-last n (map⁺ id (w ∷ zs))
  ≡⟨ Eq.cong (find-or-last n) (map⁺-cong describe-variant-preserves (w ∷ zs)) ⟩
    find-or-last n (map⁺ (⟦⟧c ∘ describe-variant) (w ∷ zs))
  ≡⟨ Eq.cong (find-or-last n) (map⁺-∘ (w ∷ zs)) ⟩
    find-or-last n (map⁺ ⟦⟧c tail-in-ccc)
  ≡⟨ Eq.sym (map-find-or-last ⟦⟧c n tail-in-ccc) ⟩
    ⟦⟧c (find-or-last n tail-in-ccc)
  ≡⟨⟩
    ⟦ find-or-last n (describe-variant w ∷ map describe-variant zs) ⟧ c
  ≡⟨⟩
    ⟦ find-or-last (suc n) (describe-variant v ∷ describe-variant w ∷ map describe-variant zs) ⟧ c
  ≡⟨⟩
    ⟦ find-or-last (c 𝔻)  (describe-variant v ∷ describe-variant w ∷ map describe-variant zs) ⟧ c
  ≡⟨⟩
    ⟦ 𝔻 ⟨ map⁺ describe-variant (v ∷ w ∷ zs) ⟩ ⟧ c
  ∎


preserves-⊇ : ∀ {A} (l : VariantList ∞ A) (c : Cᶜ) → ⟦ l ⟧ₗ (fnoc (VariantList→CCC l) c) ≡ ⟦ expr (VariantList→CCC l) ⟧ c
preserves-⊇ {A} (v ∷ []) c = describe-variant-preserves v -- This proof is the same as for the preserves-⊆ (so look there if you want to see a step by step proof)
preserves-⊇ (v ∷ w ∷ zs) c with c 𝔻
... | zero  = describe-variant-preserves v
... | suc i =
  let ⟦⟧c = flip ⟦_⟧ c
      tail = w ∷ zs
      tail-in-ccc = map⁺ describe-variant tail
  in
  begin
    find-or-last i tail
  ≡⟨ Eq.cong (find-or-last i) (Eq.sym (map⁺-id tail)) ⟩
    find-or-last i (map⁺ id tail)
  ≡⟨ Eq.cong (find-or-last i) (map⁺-cong describe-variant-preserves tail) ⟩
    find-or-last i (map⁺ (⟦⟧c ∘ describe-variant) tail)
  ≡⟨ Eq.cong (find-or-last i) (map⁺-∘ tail) ⟩
    find-or-last i (map⁺ ⟦⟧c tail-in-ccc)
  ≡⟨ Eq.sym (map-find-or-last ⟦⟧c i tail-in-ccc) ⟩
    ⟦⟧c (find-or-last i tail-in-ccc)
  ≡⟨⟩
    ⟦_⟧ (find-or-last i tail-in-ccc) c
  ≡⟨⟩
    ⟦ find-or-last i tail-in-ccc ⟧ c
  ∎

VariantList→CCC-is-variant-preserving : VariantList→CCC is-variant-preservingi-map-cong
VariantList→CCC-is-variant-preserving [ e ] = preserves-⊆ e , preserves-⊇ e

CCCL-is-at-least-as-expressive-as-VariantListL : CCCL is-at-least-as-expressive-as VariantListL
CCCL-is-at-least-as-expressive-as-VariantListL = expressiveness-by-translation VariantList→CCC VariantList→CCC-is-variant-preserving

CCCL-is-complete : Complete CCCL
CCCL-is-complete = completeness-by-expressiveness VariantList-is-Complete CCCL-is-at-least-as-expressive-as-VariantListL
```

