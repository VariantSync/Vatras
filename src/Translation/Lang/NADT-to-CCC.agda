module Translation.Lang.NADT-to-CCC where

open import Size using (Size; ∞)
import Data.EqIndexedSet as IndexedSet
import Data.List.NonEmpty as List⁺
open import Data.Product using (proj₂)
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Definitions
open import Framework.Variants using (Rose)
open import Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Framework.Variants using (VariantEncoder)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
import Util.List as List

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Lang.NADT as NADT using (NADT; NADTAsset; NADTChoice; NADTL)
open import Lang.CCC as CCC using (CCC; CCCL; _-<_>-)


translate : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → VariantEncoder (Rose ∞) (CCCL F) → NADT (Rose ∞) F i A → CCC F ∞ A
translate Variant→CCC (NADTAsset v) = LanguageCompiler.compile Variant→CCC v
translate Variant→CCC (NADTChoice f alternatives) = f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩

preserves-≗ : ∀ {i : Size} {F : 𝔽} {A : 𝔸} → (Variant→CCC : VariantEncoder (Rose ∞) (CCCL F)) → (expr : NADT (Rose ∞) F i A) → CCC.⟦ translate Variant→CCC expr ⟧ ≗ NADT.⟦ expr ⟧
preserves-≗ {A = A} Variant→CCC (NADTAsset v) config =
    CCC.⟦ translate Variant→CCC (NADTAsset v) ⟧ config
  ≡⟨⟩
    CCC.⟦ LanguageCompiler.compile Variant→CCC v ⟧ config
  ≡⟨ proj₂ (LanguageCompiler.preserves Variant→CCC v) config ⟩
    v
  ≡⟨⟩
    NADT.⟦ NADTAsset {Rose ∞} v ⟧ config
  ∎
preserves-≗ Variant→CCC (NADTChoice f alternatives) config =
    CCC.⟦ translate Variant→CCC (NADTChoice f alternatives) ⟧ config
  ≡⟨⟩
    CCC.⟦ f CCC.⟨ List⁺.map (translate Variant→CCC) alternatives ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ List.find-or-last (config f) (List⁺.map (translate Variant→CCC) alternatives) ⟧ config
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (List.map-find-or-last (translate Variant→CCC) (config f) alternatives) refl ⟨
    CCC.⟦ translate Variant→CCC (List.find-or-last (config f) alternatives) ⟧ config
  ≡⟨ preserves-≗ Variant→CCC (List.find-or-last (config f) alternatives) config ⟩
    NADT.⟦ List.find-or-last (config f) alternatives ⟧ config
  ≡⟨⟩
    NADT.⟦ NADTChoice f alternatives ⟧ config
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
