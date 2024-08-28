{-
This module shows that `NADT` is a subset of `CCC` by translating the `NADT`
constructors into their, less restrictive, `CCC` equivalent.
-}
module Vatras.Translation.Lang.NADT-to-CCC where

open import Size using (Size; ∞)
import Vatras.Data.EqIndexedSet as IndexedSet
import Data.List.NonEmpty as List⁺
open import Data.Product using (proj₂)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Framework.Relation.Function using (from; to)
open import Vatras.Framework.Variants using (VariantEncoder)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
import Vatras.Util.List as List

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Vatras.Lang.NADT as NADT using (NADT; NADTL; leaf; _⟨_⟩)
open import Vatras.Lang.CCC as CCC using (CCC; CCCL; _-<_>-)


translate : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → VariantEncoder (Rose ∞) (CCCL F) → NADT (Rose ∞) F i A → CCC F ∞ A
translate Variant→CCC (leaf v) = LanguageCompiler.compile Variant→CCC v
translate Variant→CCC (f ⟨ alternatives ⟩) = f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩

preserves-≗ : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : VariantEncoder (Rose ∞) (CCCL F)) → (expr : NADT (Rose ∞) F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≗ NADT.⟦ expr ⟧
preserves-≗ {A = A} Variant→CCC (leaf v) config =
    CCC.⟦ translate Variant→CCC (leaf v) ⟧ config
  ≡⟨⟩
    CCC.⟦ LanguageCompiler.compile Variant→CCC v ⟧ config
  ≡⟨ proj₂ (LanguageCompiler.preserves Variant→CCC v) config ⟩
    v
  ≡⟨⟩
    NADT.⟦ leaf {Rose ∞} v ⟧ config
  ∎
preserves-≗ Variant→CCC (f ⟨ alternatives ⟩) config =
    CCC.⟦ translate Variant→CCC (f ⟨ alternatives ⟩) ⟧ config
  ≡⟨⟩
    CCC.⟦ f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ List.find-or-last (config f) (List⁺.map (translate Variant→CCC) alternatives) ⟧ config
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (List.map-find-or-last (translate Variant→CCC) (config f) alternatives) refl ⟨
    CCC.⟦ translate Variant→CCC (List.find-or-last (config f) alternatives) ⟧ config
  ≡⟨ preserves-≗ Variant→CCC (List.find-or-last (config f) alternatives) config ⟩
    NADT.⟦ List.find-or-last (config f) alternatives ⟧ config
  ≡⟨⟩
    NADT.⟦ f ⟨ alternatives ⟩ ⟧ config
  ∎

preserves : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : VariantEncoder (Rose ∞) (CCCL F)) → (expr : NADT (Rose ∞) F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≅[ id ][ id ] NADT.⟦ expr ⟧
preserves Variant→CCC expr = ≗→≅[] (preserves-≗ Variant→CCC expr)

NADT→CCC : ∀ {i : Size} {F : 𝔽} → VariantEncoder (Rose ∞) (CCCL F) → LanguageCompiler (NADTL (Rose ∞) F) (CCCL F)
NADT→CCC Variant→CCC .LanguageCompiler.compile = translate Variant→CCC
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .to = id
NADT→CCC Variant→CCC .LanguageCompiler.config-compiler expr .from = id
NADT→CCC Variant→CCC .LanguageCompiler.preserves expr = ≅[]-sym (preserves Variant→CCC expr)

CCC≽NADT : ∀ {F : 𝔽} → VariantEncoder (Rose ∞) (CCCL F) → CCCL F ≽ NADTL (Rose ∞) F
CCC≽NADT Variant→CCC = expressiveness-from-compiler (NADT→CCC Variant→CCC)
