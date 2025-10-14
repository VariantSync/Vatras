{-|
This module translates `2CC` expressions to `NADT` expressions by duplicating
artifact constructors below the `2CC` choices if necessary.

This translation eliminates all sharing between the variants by effectively
enumerating all variants differentiated by a choice.
-}
module Vatras.Translation.Lang.2CC-to-ADT where

open import Size using (Size; ∞)
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.Bool as Bool using (if_then_else_)
import Data.Bool.Properties as Bool
open import Data.List as List using (List; []; _∷_; _ʳ++_)
import Data.List.Properties as List
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (𝔸; 𝔽; atoms)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Framework.Relation.Function using (from; to)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Vatras.Lang.All
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩)
open ADT using (ADT; ADTL; leaf; _⟨_,_⟩)

module Pushdown {F : 𝔽} where
  open import Vatras.Lang.ADT.Pushdown F (Rose ∞) V._-<_>- public
open Pushdown

translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → 2CC D i A
  → ADT D (Rose ∞) A
translate (a -< cs >-) = push-down-artifact a (List.map translate cs)
translate (d ⟨ l , r ⟩) = d ⟨ translate l , translate r ⟩

preserves-≗ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → ADT.⟦ translate expr ⟧ ≗ 2CC.⟦ expr ⟧
preserves-≗ (a -< cs >-) config =
    ADT.⟦ translate (a -< cs >-) ⟧ config
  ≡⟨⟩
    ADT.⟦ push-down-artifact a (List.map translate cs) ⟧ config
  ≡⟨ ⟦push-down-artifact⟧ a (List.map translate cs) config ⟩
    a V.-< List.map (λ e → ADT.⟦ e ⟧ config) (List.map translate cs) >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → ADT.⟦ translate e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-≗ e config) cs) ⟩
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ config) cs >-
  ≡⟨⟩
    2CC.⟦ a -< cs >- ⟧ config
  ∎
preserves-≗ (d ⟨ l , r ⟩) config =
    ADT.⟦ translate (d ⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    ADT.⟦ d ⟨ translate l , translate r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then ADT.⟦ translate l ⟧ config else ADT.⟦ translate r ⟧ config)
  ≡⟨ Bool.if-cong₂ _ (preserves-≗ l config) (preserves-≗ r config) ⟩
    2CC.⟦ d ⟨ l , r ⟩ ⟧ config
  ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → ADT.⟦ translate expr ⟧ ≅[ id ][ id ] 2CC.⟦ expr ⟧
preserves expr = ≗→≅[] (preserves-≗ expr)

2CC→ADT : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (2CCL D {i}) (ADTL D (Rose ∞))
2CC→ADT .LanguageCompiler.compile = translate
2CC→ADT .LanguageCompiler.config-compiler expr .to = id
2CC→ADT .LanguageCompiler.config-compiler expr .from = id
2CC→ADT .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

ADT≽2CC : ∀ {D : 𝔽} → ADTL D (Rose ∞) ≽ 2CCL D
ADT≽2CC = expressiveness-from-compiler 2CC→ADT
