{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_)
open import Construct.Artifact using () renaming (Syntax to Artifact)

module Translation.Lang.NADT-to-CCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Construct.Choices
open import Construct.GrulerArtifacts using (leaf)
import Data.EqIndexedSet as IndexedSet
import Data.List.NonEmpty as List⁺
open import Data.Product using (proj₂)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Definitions
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Framework.Variants using (VariantEncoder)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
open import Size using (Size; ∞)
import Util.List as List

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Lang.All.Generic Variant Artifact∈ₛVariant
open NADT using (NADT; NADTAsset; NADTChoice; NADTL)
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)


translate : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → VariantEncoder Variant (CCCL F) → NADT Variant F i A → CCC F ∞ A
translate Variant→CCC (NADTAsset (leaf v)) = LanguageCompiler.compile Variant→CCC v
translate Variant→CCC (NADTChoice (f Choice.⟨ alternatives ⟩)) = f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩

preserves-≗ : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : VariantEncoder Variant (CCCL F)) → (expr : NADT Variant F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≗ NADT.⟦ expr ⟧
preserves-≗ {A = A} Variant→CCC (NADTAsset (leaf v)) config =
    CCC.⟦ translate Variant→CCC (NADTAsset (leaf v)) ⟧ config
  ≡⟨⟩
    CCC.⟦ LanguageCompiler.compile Variant→CCC v ⟧ config
  ≡⟨ proj₂ (LanguageCompiler.preserves Variant→CCC v) config ⟩
    v
  ≡⟨⟩
    NADT.⟦ NADTAsset {Variant} (leaf v) ⟧ config
  ∎
preserves-≗ Variant→CCC (NADTChoice (f Choice.⟨ alternatives ⟩)) config =
    CCC.⟦ translate Variant→CCC (NADTChoice (f Choice.⟨ alternatives ⟩)) ⟧ config
  ≡⟨⟩
    CCC.⟦ f ⟨ List⁺.map (translate Variant→CCC) alternatives ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ List.find-or-last (config f) (List⁺.map (translate Variant→CCC) alternatives) ⟧ config
  ≡˘⟨ Eq.cong₂ CCC.⟦_⟧ (List.map-find-or-last (translate Variant→CCC) (config f) alternatives) refl ⟩
    CCC.⟦ translate Variant→CCC (List.find-or-last (config f) alternatives) ⟧ config
  ≡⟨ preserves-≗ Variant→CCC (List.find-or-last (config f) alternatives) config ⟩
    NADT.⟦ List.find-or-last (config f) alternatives ⟧ config
  ≡⟨⟩
    NADT.⟦ NADTChoice (f Choice.⟨ alternatives ⟩) ⟧ config
  ∎

preserves : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : VariantEncoder Variant (CCCL F)) → (expr : NADT Variant F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≅[ id ][ id ] NADT.⟦ expr ⟧
preserves Variant→CCC expr = ≗→≅[] (preserves-≗ Variant→CCC expr)

NADT→CCC : ∀ {i : Size} {F : 𝔽} → VariantEncoder Variant (CCCL F) → LanguageCompiler (NADTL Variant F) (CCCL F)
NADT→CCC Variant→CCC .LanguageCompiler.compile = translate Variant→CCC
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .to = id
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .from = id
NADT→CCC Variant→CCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves Variant→CCC expr)

CCC≽NADT : ∀ {F : 𝔽} → VariantEncoder Variant (CCCL F) → CCCL F ≽ NADTL Variant F
CCC≽NADT Variant→CCC = expressiveness-from-compiler (NADT→CCC Variant→CCC)
