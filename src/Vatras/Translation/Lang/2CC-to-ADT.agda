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
open 2CC using () renaming (2CC to 2CCSyntax) -- Necessary for disambiguation
open 2CC using (2CC; 2CCL)
open ADT using (ADT; ADTL; leaf; _⟨_,_⟩)

push-down-artifact : ∀ {i : Size} {D : 𝔽} {A : 𝔸} → atoms A → List (ADT (Rose ∞) D A) → ADT (Rose ∞) D A
push-down-artifact {A = A} a cs = go cs []
  module push-down-artifact-Implementation where
  go : ∀ {i : Size} {D : 𝔽} → List (ADT (Rose ∞) D A) → List (Rose ∞ A) → ADT (Rose ∞) D A
  go [] vs = leaf (a V.-< List.reverse vs >-)
  go (leaf v ∷ cs) vs = go cs (v ∷ vs)
  go (d ⟨ c₁ , c₂ ⟩ ∷ cs) vs = d ⟨ go (c₁ ∷ cs) vs , go (c₂ ∷ cs) vs ⟩

translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → 2CC D i A
  → ADT (Rose ∞) D A
translate (a 2CC.-< cs >-) = push-down-artifact a (List.map translate cs)
translate (d 2CC.⟨ l , r ⟩) = d ⟨ translate l , translate r ⟩

⟦push-down-artifact⟧ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (a : atoms A)
  → (cs : List (ADT (Rose ∞) D A))
  → (config : ADT.Configuration D)
  → ADT.⟦ push-down-artifact a cs ⟧ config ≡ a V.-< List.map (λ e → ADT.⟦ e ⟧ config) cs >-
⟦push-down-artifact⟧ {D = D} {A = A} a cs config = go' cs []
  where
  open push-down-artifact-Implementation

  go' : ∀ {i : Size}
    → (cs' : List (ADT (Rose ∞) D A))
    → (vs : List (Rose ∞ A))
    → ADT.⟦ go a cs cs' vs ⟧ config ≡ a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) cs' >-
  go' [] vs = Eq.sym (Eq.cong₂ V._-<_>- refl (Eq.trans (List.ʳ++-defn vs) (List.++-identityʳ (List.reverse vs))))
  go' (leaf v ∷ cs') vs = Eq.trans (go' cs' (v ∷ vs)) (Eq.cong₂ V._-<_>- refl (List.++-ʳ++ List.[ v ] {ys = vs}))
  go' ((d ⟨ c₁ , c₂ ⟩) ∷ cs') vs =
      ADT.⟦ d ⟨ go a cs (c₁ ∷ cs') vs , go a cs (c₂ ∷ cs') vs ⟩ ⟧ config
    ≡⟨⟩
      (if config d
        then ADT.⟦ go a cs (c₁ ∷ cs') vs ⟧ config
        else ADT.⟦ go a cs (c₂ ∷ cs') vs ⟧ config)
    ≡⟨ Eq.cong₂ (if config d then_else_) (go' (c₁ ∷ cs') vs) (go' (c₂ ∷ cs') vs) ⟩
      (if config d
        then a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) (c₁ ∷ cs') >-
        else a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) (c₂ ∷ cs') >-)
    ≡⟨ Bool.if-float (λ c → a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) (c ∷ cs') >-) (config d) ⟨
      a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) ((if config d then c₁ else c₂) ∷ cs') >-
    ≡⟨⟩
      a V.-< vs ʳ++ ADT.⟦ if config d then c₁ else c₂ ⟧ config ∷ List.map (λ e → ADT.⟦ e ⟧ config) cs' >-
    ≡⟨ Eq.cong₂ V._-<_>- refl (Eq.cong₂ _ʳ++_ {x = vs} refl (Eq.cong₂ _∷_ (Bool.if-float (λ e → ADT.⟦ e ⟧ config) (config d)) refl)) ⟩
      a V.-< vs ʳ++ (if config d then ADT.⟦ c₁ ⟧ config else ADT.⟦ c₂ ⟧ config) ∷ List.map (λ e → ADT.⟦ e ⟧ config) cs' >-
    ≡⟨⟩
      a V.-< vs ʳ++ ADT.⟦ d ⟨ c₁ , c₂ ⟩ ⟧ config ∷ List.map (λ e → ADT.⟦ e ⟧ config) cs' >-
    ≡⟨⟩
      a V.-< vs ʳ++ List.map (λ e → ADT.⟦ e ⟧ config) (d ⟨ c₁ , c₂ ⟩ ∷ cs') >-
    ∎

preserves-≗ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → ADT.⟦ translate expr ⟧ ≗ 2CC.⟦ expr ⟧
preserves-≗ {D = D} {A = A} (a 2CC.-< cs >-) config =
    ADT.⟦ translate (a 2CCSyntax.-< cs >-) ⟧ config
  ≡⟨⟩
    ADT.⟦ push-down-artifact a (List.map translate cs) ⟧ config
  ≡⟨ ⟦push-down-artifact⟧ a (List.map translate cs) config ⟩
    a V.-< List.map (λ e → ADT.⟦ e ⟧ config) (List.map translate cs) >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → ADT.⟦ translate e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-≗ e config) cs) ⟩
    a V.-< List.map (λ e → 2CC.⟦ e ⟧ config) cs >-
  ≡⟨⟩
    2CC.⟦ a 2CCSyntax.-< cs >- ⟧ config
  ∎
preserves-≗ (d 2CC.⟨ l , r ⟩) config =
    ADT.⟦ translate (d 2CCSyntax.⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    ADT.⟦ d ⟨ translate l , translate r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then ADT.⟦ translate l ⟧ config else ADT.⟦ translate r ⟧ config)
  ≡⟨ Eq.cong₂ (if config d then_else_) (preserves-≗ l config) (preserves-≗ r config) ⟩
    2CC.⟦ d 2CCSyntax.⟨ l , r ⟩ ⟧ config
  ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → ADT.⟦ translate expr ⟧ ≅[ id ][ id ] 2CC.⟦ expr ⟧
preserves expr = ≗→≅[] (preserves-≗ expr)

2CC→ADT : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (2CCL D {i}) (ADTL (Rose ∞) D)
2CC→ADT .LanguageCompiler.compile = translate
2CC→ADT .LanguageCompiler.config-compiler expr .to = id
2CC→ADT .LanguageCompiler.config-compiler expr .from = id
2CC→ADT .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

ADT≽2CC : ∀ {D : 𝔽} → ADTL (Rose ∞) D ≽ 2CCL D
ADT≽2CC = expressiveness-from-compiler 2CC→ADT
