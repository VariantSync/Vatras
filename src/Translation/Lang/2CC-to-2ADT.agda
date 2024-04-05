{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Framework.Definitions using (𝔸; 𝔽; 𝕍; atoms)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.2CC-to-2ADT (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

import Data.EqIndexedSet as IndexedSet
open import Data.Bool as Bool using (if_then_else_)
import Data.Bool.Properties as Bool
open import Data.List as List using (List; []; _∷_; _ʳ++_)
import Data.List.Properties as List
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)
open import Size using (Size)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; ≅[]-sym; ≗→≅[])

open import Lang.All.Generic Variant Artifact∈ₛVariant
open 2CC using (2CC; 2CCL)
open 2ADT using (2ADT; 2ADTL; leaf; _⟨_,_⟩)

artifact : ∀ {A : 𝔸} → atoms A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


push-down-artifact : ∀ {i : Size} {D : 𝔽} {A : 𝔸} → atoms A → List (2ADT Variant D A) → 2ADT Variant D A
push-down-artifact {A = A} a cs = go cs []
  module push-down-artifact-Implementation where
  go : ∀ {i : Size} {D : 𝔽} → List (2ADT Variant D A) → List (Variant A) → 2ADT Variant D A
  go [] vs = leaf (artifact a (List.reverse vs))
  go (leaf v ∷ cs) vs = go cs (v ∷ vs)
  go (d ⟨ c₁ , c₂ ⟩ ∷ cs) vs = d ⟨ go (c₁ ∷ cs) vs , go (c₂ ∷ cs) vs ⟩

translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → 2CC D i A
  → 2ADT Variant D A
translate (a 2CC.-< cs >-) = push-down-artifact a (List.map translate cs)
translate (d 2CC.⟨ l , r ⟩) = d ⟨ translate l , translate r ⟩

⟦push-down-artifact⟧ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (a : atoms A)
  → (cs : List (2ADT Variant D A))
  → (config : 2ADT.Configuration D)
  → 2ADT.⟦ push-down-artifact a cs ⟧ config ≡ artifact a (List.map (λ e → 2ADT.⟦ e ⟧ config) cs)
⟦push-down-artifact⟧ {D = D} {A = A} a cs config = go' cs []
  where
  open push-down-artifact-Implementation

  go' : ∀ {i : Size}
    → (cs' : List (2ADT Variant D A))
    → (vs : List (Variant A))
    → 2ADT.⟦ go a cs cs' vs ⟧ config ≡ artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) cs')
  go' [] vs = Eq.sym (Eq.cong₂ artifact refl (Eq.trans (List.ʳ++-defn vs) (List.++-identityʳ (List.reverse vs))))
  go' (leaf v ∷ cs') vs = Eq.trans (go' cs' (v ∷ vs)) (Eq.cong₂ artifact refl (List.ʳ++-++ List.[ v ] {ys = vs}))
  go' ((d ⟨ c₁ , c₂ ⟩) ∷ cs') vs =
      2ADT.⟦ d ⟨ go a cs (c₁ ∷ cs') vs , go a cs (c₂ ∷ cs') vs ⟩ ⟧ config
    ≡⟨⟩
      (if config d
        then 2ADT.⟦ go a cs (c₁ ∷ cs') vs ⟧ config
        else 2ADT.⟦ go a cs (c₂ ∷ cs') vs ⟧ config)
    ≡⟨ Eq.cong₂ (if config d then_else_) (go' (c₁ ∷ cs') vs) (go' (c₂ ∷ cs') vs) ⟩
      (if config d
        then artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) (c₁ ∷ cs'))
        else artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) (c₂ ∷ cs')))
    ≡˘⟨ Bool.push-function-into-if (λ c → artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) (c ∷ cs'))) (config d) ⟩
      artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) ((if config d then c₁ else c₂) ∷ cs'))
    ≡⟨⟩
      artifact a (vs ʳ++ 2ADT.⟦ if config d then c₁ else c₂ ⟧ config ∷ List.map (λ e → 2ADT.⟦ e ⟧ config) cs')
    ≡⟨ Eq.cong₂ artifact refl (Eq.cong₂ _ʳ++_ {x = vs} refl (Eq.cong₂ _∷_ (Bool.push-function-into-if (λ e → 2ADT.⟦ e ⟧ config) (config d)) refl)) ⟩
      artifact a (vs ʳ++ (if config d then 2ADT.⟦ c₁ ⟧ config else 2ADT.⟦ c₂ ⟧ config) ∷ List.map (λ e → 2ADT.⟦ e ⟧ config) cs')
    ≡⟨⟩
      artifact a (vs ʳ++ 2ADT.⟦ d ⟨ c₁ , c₂ ⟩ ⟧ config ∷ List.map (λ e → 2ADT.⟦ e ⟧ config) cs')
    ≡⟨⟩
      artifact a (vs ʳ++ List.map (λ e → 2ADT.⟦ e ⟧ config) (d ⟨ c₁ , c₂ ⟩ ∷ cs'))
    ∎

preserves-≗ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → 2ADT.⟦ translate expr ⟧ ≗ 2CC.⟦ expr ⟧
preserves-≗ {D = D} {A = A} (a 2CC.-< cs >-) config =
    2ADT.⟦ translate (a 2CC.-< cs >-) ⟧ config
  ≡⟨⟩
    2ADT.⟦ push-down-artifact a (List.map translate cs) ⟧ config
  ≡⟨ ⟦push-down-artifact⟧ a (List.map translate cs) config ⟩
    artifact a (List.map (λ e → 2ADT.⟦ e ⟧ config) (List.map translate cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → 2ADT.⟦ translate e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-≗ e config) cs) ⟩
    artifact a (List.map (λ e → 2CC.⟦ e ⟧ config) cs)
  ≡⟨⟩
    2CC.⟦ a 2CC.-< cs >- ⟧ config
  ∎
preserves-≗ (d 2CC.⟨ l , r ⟩) config =
    2ADT.⟦ translate (d 2CC.⟨ l , r ⟩) ⟧ config
  ≡⟨⟩
    2ADT.⟦ d ⟨ translate l , translate r ⟩ ⟧ config
  ≡⟨⟩
    (if config d then 2ADT.⟦ translate l ⟧ config else 2ADT.⟦ translate r ⟧ config)
  ≡˘⟨ Bool.push-function-into-if (λ e → 2ADT.⟦ translate e ⟧ config) (config d) ⟩
    2ADT.⟦ translate (if config d then l else r) ⟧ config
  ≡⟨ preserves-≗ (if config d then l else r) config ⟩
    2CC.⟦ if config d then l else r ⟧ config
  ≡⟨⟩
    2CC.⟦ d 2CC.⟨ l , r ⟩ ⟧ config
  ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (expr : 2CC D i A)
  → 2ADT.⟦ translate expr ⟧ ≅[ id ][ id ] 2CC.⟦ expr ⟧
preserves expr = ≗→≅[] (preserves-≗ expr)

2CC→2ADT : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (2CCL {i} D) (2ADTL Variant D)
2CC→2ADT .LanguageCompiler.compile = translate
2CC→2ADT .LanguageCompiler.config-compiler expr .to = id
2CC→2ADT .LanguageCompiler.config-compiler expr .from = id
2CC→2ADT .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)

2ADT≽2CC : ∀ {D : 𝔽} → 2ADTL Variant D ≽ 2CCL D
2ADT≽2CC = expressiveness-from-compiler 2CC→2ADT
