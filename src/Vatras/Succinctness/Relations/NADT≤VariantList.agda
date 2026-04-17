open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _>_; z≤n; s≤s)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)

module Vatras.Succinctness.Relations.NADT≤VariantList (F : 𝔽) (V : 𝕍) (sizeV : ∀ {A : 𝔸} → V A → ℕ) (sizeV>0 : ∀ {A} (v : V A) → sizeV v > 0) (f : F) where

open import Data.Product using (_,_; proj₁; proj₂)
import Data.Nat.Properties as ℕ
open import Data.List using ([]; _∷_; map; sum; length)
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open import Function using (const; _∘_)
open import Size using (∞)

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]→≅)
open import Vatras.Util.List as List using (find-or-last)
open import Vatras.Succinctness.ProofDefinition V using (_≤ₛ_)
open import Vatras.Succinctness.Sizes using (SizedVariantList; sizeVariantList; SizedNADT; sizeNADT)
open import Vatras.Lang.All.Fixed F V
open VariantList using (VariantList)
open NADT using (NADT; _⟨_⟩; leaf)

translate : ∀ {A : 𝔸} → VariantList A → NADT ∞ A
translate vs = f ⟨ List⁺.map leaf vs ⟩

translate-preserves-⊆ : ∀ {A : 𝔸} → (vs : VariantList A) → NADT.⟦ translate vs ⟧ ⊆[ (λ c → c f) ] VariantList.⟦ vs ⟧
translate-preserves-⊆ vs config =
    NADT.⟦ translate vs ⟧ config
  ≡⟨⟩
    NADT.⟦ find-or-last (config f) (List⁺.map leaf vs) ⟧ config
  ≡⟨ Eq.cong (λ x → NADT.⟦ x ⟧ config) (List.map-find-or-last leaf (config f) vs) ⟨
    NADT.⟦ leaf (find-or-last (config f) vs) ⟧ config
  ≡⟨⟩
    find-or-last (config f) vs
  ≡⟨⟩
    VariantList.⟦ vs ⟧ (config f)
  ∎
  where
  open Eq.≡-Reasoning

translate-preserves-⊇ : ∀ {A : 𝔸} → (vs : VariantList A) → VariantList.⟦ vs ⟧ ⊆[ const ] NADT.⟦ translate vs ⟧
translate-preserves-⊇ vs i =
    VariantList.⟦ vs ⟧ i
  ≡⟨⟩
    find-or-last i vs
  ≡⟨⟩
    NADT.⟦ leaf (find-or-last i vs) ⟧ (const i)
  ≡⟨ Eq.cong (λ x → NADT.⟦ x ⟧ (const i)) (List.map-find-or-last leaf i vs) ⟩
    NADT.⟦ find-or-last i (List⁺.map leaf vs) ⟧ (const i)
  ≡⟨⟩
    NADT.⟦ translate vs ⟧ (const i)
  ∎
  where
  open Eq.≡-Reasoning

translate-preserves : ∀ {A : 𝔸} → (vs : VariantList A) → NADT.⟦ translate vs ⟧ ≅[ (λ c → c f) ][ const ] VariantList.⟦ vs ⟧
translate-preserves vs = translate-preserves-⊆ vs , translate-preserves-⊇ vs

lemma : ∀ {A : 𝔸} (vs : VariantList A) → sizeNADT sizeV (translate vs) ≤ 3 * sizeVariantList {V} sizeV vs
lemma {A} vs =
  begin
    sizeNADT sizeV (translate vs)
  ≡⟨⟩
    suc (sum (map (sizeNADT sizeV) (List⁺.toList (List⁺.map leaf vs))))
  ≡⟨⟩
    suc (sum (map (sizeNADT sizeV) (map leaf (List⁺.toList vs))))
  ≡⟨ Eq.cong (λ x → suc (sum x)) (List.map-∘ {g = sizeNADT sizeV} {f = leaf} (List⁺.toList vs)) ⟨
    suc (sum (map (sizeNADT sizeV ∘ leaf) (List⁺.toList vs)))
  ≡⟨⟩
    suc (sum (map (λ v → suc (sizeV v)) (List⁺.toList vs)))
  ≡⟨ Eq.cong (λ x → suc (sum x)) (List.map-∘ {g = suc} (List⁺.toList vs)) ⟩
    suc (sum (map suc (map sizeV (List⁺.toList vs))))
  ≡⟨ Eq.cong suc (List.sum-+ 1 (map sizeV (List⁺.toList vs))) ⟩
    suc (1 * length (map sizeV (List⁺.toList vs)) + sum (map sizeV (List⁺.toList vs)))
  ≡⟨ Eq.cong (λ x → suc (x + sum (map sizeV (List⁺.toList vs)))) (ℕ.*-identityˡ (length (map sizeV (List⁺.toList vs)))) ⟩
    suc (length (map sizeV (List⁺.toList vs)) + sum (map sizeV (List⁺.toList vs)))
  ≡⟨ Eq.cong (λ x → suc (x + sum (map sizeV (List⁺.toList vs)))) (List.length-map sizeV (List⁺.toList vs)) ⟩
    suc (List⁺.length vs + sum (map sizeV (List⁺.toList vs)))
  ≡⟨⟩
    1 + List⁺.length vs + sum (map sizeV (List⁺.toList vs))
  ≤⟨ ℕ.+-monoˡ-≤ (sum (map sizeV (List⁺.toList vs))) (ℕ.+-monoˡ-≤ (List⁺.length vs) (s≤s (z≤n {length (List⁺.tail vs)}))) ⟩
    List⁺.length vs + List⁺.length vs + sum (map sizeV (List⁺.toList vs))
  ≡⟨ Eq.cong (λ x → (List⁺.length vs + x) + sum (map sizeV (List⁺.toList vs))) (ℕ.+-identityʳ (List⁺.length vs)) ⟨
    List⁺.length vs + (List⁺.length vs + 0) + sum (map sizeV (List⁺.toList vs))
  ≡⟨⟩
    2 * List⁺.length vs + sum (map sizeV (List⁺.toList vs))
  ≡⟨ Eq.cong (λ x → 2 * x + sum (map sizeV (List⁺.toList vs))) (ℕ.*-identityˡ (List⁺.length vs)) ⟨
    2 * (1 * List⁺.length vs) + sum (map sizeV (List⁺.toList vs))
  ≡⟨ Eq.cong (λ x → 2 * x + sum (map sizeV (List⁺.toList vs))) (List.sum-map-const 1 (List⁺.toList vs)) ⟨
    2 * sum (map (const 1) (List⁺.toList vs)) + sum (map sizeV (List⁺.toList vs))
  ≤⟨ ℕ.+-monoˡ-≤ (sum (map sizeV (List⁺.toList vs))) (ℕ.*-monoʳ-≤ 2 (List.sum-map-≤ (const 1) sizeV (List⁺.toList vs) sizeV>0)) ⟩
    2 * sum (map sizeV (List⁺.toList vs)) + sum (map sizeV (List⁺.toList vs))
  ≡⟨ Eq.cong (2 * sum (map sizeV (List⁺.toList vs)) +_) (ℕ.*-identityˡ (sum (map sizeV (List⁺.toList vs)))) ⟨
    2 * sum (map sizeV (List⁺.toList vs)) + 1 * sum (map sizeV (List⁺.toList vs))
  ≡⟨ ℕ.*-distribʳ-+ (sum (map sizeV (List⁺.toList vs))) 2 1 ⟨
    3 * sum (map sizeV (List⁺.toList vs))
  ≡⟨⟩
    3 * sizeVariantList {V} sizeV vs
  ∎
  where
  open ℕ.≤-Reasoning

NADT≤VariantList : SizedNADT F V sizeV ≤ₛ SizedVariantList V sizeV
NADT≤VariantList .proj₁ = 3
NADT≤VariantList .proj₂ A vs vs-translatable = translate vs , ≅[]→≅ (translate-preserves vs) , lemma {A} vs
