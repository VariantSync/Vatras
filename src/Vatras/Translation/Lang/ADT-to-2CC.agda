{-|
This module shows that `ADT` is a subset of `2CC` by translating the `ADT`
constructors into their, less restrictive, `2CC` equivalent.
-}
module Vatras.Translation.Lang.ADT-to-2CC where

open import Size using (Size; ∞)
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.Bool as Bool using (if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Product using (proj₂)
open import Data.List as List using (List; []; _∷_; _ʳ++_)
import Data.List.Properties as List
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Framework.Relation.Function using (from; to)
open import Vatras.Framework.Variants using (VariantEncoder)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)

open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Vatras.Lang.2CC as 2CC using (2CC; 2CCL)
open import Vatras.Lang.ADT as ADT using (ADT; ADTL; leaf; _⟨_,_⟩)

translate : ∀ {F : 𝔽} {A : 𝔸} → VariantEncoder (Rose ∞) (2CCL F) → ADT (Rose ∞) F A → 2CC F ∞ A
translate Variant→2CC (ADT.leaf v) = LanguageCompiler.compile Variant→2CC v
translate Variant→2CC (f ADT.⟨ l , r ⟩) = f 2CC.⟨ translate Variant→2CC l , translate Variant→2CC r ⟩

preserves-≗ : ∀ {F : 𝔽} {A : 𝔸} → (Variant→2CC : VariantEncoder (Rose ∞) (2CCL F)) → (expr : ADT (Rose ∞) F A) → 2CC.⟦ translate Variant→2CC expr ⟧ ≗ ADT.⟦ expr ⟧
preserves-≗ {A = A} Variant→2CC (ADT.leaf v) config =
    2CC.⟦ translate Variant→2CC (leaf v) ⟧ config
  ≡⟨⟩
    2CC.⟦ LanguageCompiler.compile Variant→2CC v ⟧ config
  ≡⟨ proj₂ (LanguageCompiler.preserves Variant→2CC v) config ⟩
    v
  ≡⟨⟩
    ADT.⟦ leaf {Rose ∞} v ⟧ config
  ∎
preserves-≗ Variant→2CC (f ADT.⟨ l , r ⟩) config =
    2CC.⟦ translate Variant→2CC (f ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    2CC.⟦ f 2CC.⟨ translate Variant→2CC l , translate Variant→2CC r ⟩ ⟧ config
  ≡⟨⟩
    (if config f then 2CC.⟦ translate Variant→2CC l ⟧ config else 2CC.⟦ translate Variant→2CC r ⟧ config)
  ≡⟨ Eq.cong₂ (if config f then_else_) (preserves-≗ Variant→2CC l config) (preserves-≗ Variant→2CC r config) ⟩
    (if config f then ADT.⟦ l ⟧ config else ADT.⟦ r ⟧ config)
  ≡⟨⟩
    ADT.⟦ f ⟨ l , r ⟩ ⟧ config
  ∎

preserves : ∀ {F : 𝔽} {A : 𝔸} → (Variant→2CC : VariantEncoder (Rose ∞) (2CCL F)) → (expr : ADT (Rose ∞) F A) → 2CC.⟦ translate Variant→2CC expr ⟧ ≅[ id ][ id ] ADT.⟦ expr ⟧
preserves Variant→2CC expr = ≗→≅[] (preserves-≗ Variant→2CC expr)

ADT→2CC : ∀ {F : 𝔽} → VariantEncoder (Rose ∞) (2CCL F) → LanguageCompiler (ADTL (Rose ∞) F) (2CCL F)
ADT→2CC Variant→2CC .LanguageCompiler.compile = translate Variant→2CC
ADT→2CC Variant→2CC .LanguageCompiler.config-compiler expr .to = id
ADT→2CC Variant→2CC .LanguageCompiler.config-compiler expr .from = id
ADT→2CC Variant→2CC .LanguageCompiler.preserves expr = ≅[]-sym (preserves Variant→2CC expr)

2CC≽ADT : ∀ {F : 𝔽} → VariantEncoder (Rose ∞) (2CCL F) → 2CCL F ≽ ADTL (Rose ∞) F
2CC≽ADT Variant→2CC = expressiveness-from-compiler (ADT→2CC Variant→2CC)
