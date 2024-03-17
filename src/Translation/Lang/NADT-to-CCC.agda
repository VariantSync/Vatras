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
open import Framework.Variants using (Variant-is-VL)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
open import Size using (Size; ∞)
import Util.List as List

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

import Lang.NADT
module NADT where
  open Lang.NADT Variant using (NADT; NADTAsset; NADTChoice) renaming (NADTVL to NADTL) public
  module NADT-Sem {F} = Lang.NADT Variant F
  open NADT-Sem using () renaming (semantics to ⟦_⟧) public -- TODO
open NADT using (NADT; NADTAsset; NADTChoice; NADTL)

import Lang.CCC
module CCC where
  open Lang.CCC public
  module CCC-Sem-1 F = Lang.CCC.Sem F Variant Artifact∈ₛVariant
  open CCC-Sem-1 using (CCCL) public
  module CCC-Sem-2 {F} = Lang.CCC.Sem F Variant Artifact∈ₛVariant
  open CCC-Sem-2 using (⟦_⟧) public
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)


translate : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → LanguageCompiler (Variant-is-VL Variant) (CCCL F) → NADT F i A → CCC F ∞ A
translate Variant→CCC (NADTAsset (leaf v)) = LanguageCompiler.compile Variant→CCC v
translate Variant→CCC (NADTChoice (f Choice.⟨ alternatives ⟩)) = f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩

preserves-≗ : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : LanguageCompiler (Variant-is-VL Variant) (CCCL F)) → (expr : NADT F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≗ NADT.⟦ expr ⟧
preserves-≗ {A = A} Variant→CCC (NADTAsset (leaf v)) config =
    CCC.⟦ translate Variant→CCC (NADTAsset (leaf v)) ⟧ config
  ≡⟨⟩
    CCC.⟦ LanguageCompiler.compile Variant→CCC v ⟧ config
  ≡⟨ proj₂ (LanguageCompiler.preserves Variant→CCC v) config ⟩
    v
  ≡⟨⟩
    NADT.⟦ NADTAsset (leaf v) ⟧ config
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

preserves : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : LanguageCompiler (Variant-is-VL Variant) (CCCL F)) → (expr : NADT F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≅[ id ][ id ] NADT.⟦ expr ⟧
preserves Variant→CCC expr = ≗→≅[] (preserves-≗ Variant→CCC expr)

NADT→CCC : ∀ {i : Size} {F : 𝔽} → LanguageCompiler (Variant-is-VL Variant) (CCCL F) → LanguageCompiler (NADTL F) (CCCL F)
NADT→CCC Variant→CCC .LanguageCompiler.compile = translate Variant→CCC
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .to = id
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .from = id
NADT→CCC Variant→CCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves Variant→CCC expr)

CCC≽NADT : ∀ {F : 𝔽} → LanguageCompiler (Variant-is-VL Variant) (CCCL F) → CCCL F ≽ NADTL F
CCC≽NADT Variant→CCC = expressiveness-from-compiler (NADT→CCC Variant→CCC)
