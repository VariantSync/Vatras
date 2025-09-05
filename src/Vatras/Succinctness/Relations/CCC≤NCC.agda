open import Vatras.Framework.Definitions using (𝔽; 𝔸; atomSize)
module Vatras.Succinctness.Relations.CCC≤NCC (F : 𝔽) where

open import Data.Nat as ℕ using (suc; _≤_; s≤s; _+_)
import Data.Nat.Properties as ℕ
import Data.List as List
open import Data.Vec as Vec using (_∷_)
import Data.Vec.Properties as Vec
import Data.List.Properties as List
import Data.List.NonEmpty as List⁺
open import Data.Product using (_,_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (≅-sym; ≅[]→≅)
open import Vatras.Framework.Variants using (Rose)
import Vatras.Util.List as List
open import Vatras.Util.Nat.AtLeast using (ℕ≥; sucs)
import Vatras.Util.Vec as Vec
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Translation.LanguageMap using (NCC→CCC)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≤Size_)
open import Vatras.Succinctness.Sizes using (SizedNCC; sizeNCC; SizedCCC; sizeCCC)

lemma : ∀ {i : Size} {A : 𝔸} (n : ℕ≥ 2) (ncc : NCC.NCC n i A) → sizeCCC (LanguageCompiler.compile (NCC→CCC n) ncc) ≤ sizeNCC n ncc
lemma {A = A} (sucs n) (a NCC.NCC.-< cs >-) =
  begin
    sizeCCC (LanguageCompiler.compile (NCC→CCC (sucs n)) (a NCC.NCC.-< cs >-))
  ≡⟨⟩
    sizeCCC (a CCC.CCC.-< List.map (LanguageCompiler.compile (NCC→CCC (sucs n))) cs >-)
  ≡⟨⟩
    suc (atomSize A a + List.sum (List.map sizeCCC (List.map (LanguageCompiler.compile (NCC→CCC (sucs n))) cs)))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
    suc (atomSize A a + List.sum (List.map (sizeCCC ∘ LanguageCompiler.compile (NCC→CCC (sucs n))) cs))
  ≤⟨ s≤s (ℕ.+-monoʳ-≤ (atomSize A a) (List.sum-map-≤ (sizeCCC ∘ LanguageCompiler.compile (NCC→CCC (sucs n))) (sizeNCC (sucs n)) cs (lemma (sucs n)))) ⟩
    suc (atomSize A a + List.sum (List.map (sizeNCC (sucs n)) cs))
  ≡⟨⟩
    sizeNCC (sucs n) (a NCC.NCC.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
lemma (sucs n) (D NCC.NCC.⟨ c ∷ cs ⟩) =
  begin
    sizeCCC (LanguageCompiler.compile (NCC→CCC (sucs n)) (D NCC.NCC.⟨ c ∷ cs ⟩))
  ≡⟨⟩
    sizeCCC (D CCC.⟨ List⁺.fromVec (Vec.map (LanguageCompiler.compile (NCC→CCC (sucs n))) (c ∷ cs)) ⟩)
  ≡⟨⟩
    suc (List.sum (List.map sizeCCC (List⁺.toList (List⁺.fromVec (Vec.map (LanguageCompiler.compile (NCC→CCC (sucs n))) (c ∷ cs))))))
  ≡⟨⟩
    suc (List.sum (List.map sizeCCC (Vec.toList (Vec.map (LanguageCompiler.compile (NCC→CCC (sucs n))) (c ∷ cs)))))
  ≡⟨ Eq.cong (λ x → suc (List.sum (List.map sizeCCC x))) (Vec.toList-map (LanguageCompiler.compile (NCC→CCC (sucs n))) (c ∷ cs)) ⟩
    suc (List.sum (List.map sizeCCC (List.map (LanguageCompiler.compile (NCC→CCC (sucs n))) (Vec.toList (c ∷ cs)))))
  ≡⟨ Eq.cong (λ x → suc (List.sum x)) (List.map-∘ (Vec.toList (c ∷ cs))) ⟨
    suc (List.sum (List.map (sizeCCC ∘ LanguageCompiler.compile (NCC→CCC (sucs n))) (Vec.toList (c ∷ cs))))
  ≤⟨ s≤s (List.sum-map-≤ (sizeCCC ∘ LanguageCompiler.compile (NCC→CCC (sucs n))) (sizeNCC (sucs n)) (Vec.toList (c ∷ cs)) (lemma (sucs n))) ⟩
    suc (List.sum (List.map (sizeNCC (sucs n)) (Vec.toList (c ∷ cs))))
  ≡⟨ Eq.cong (λ x → suc (List.sum x)) (Vec.toList-map (sizeNCC (sucs n)) (c ∷ cs)) ⟨
    suc (List.sum (Vec.toList (Vec.map (sizeNCC (sucs n)) (c ∷ cs))))
  ≡⟨ Eq.cong suc (Vec.sum-toList (Vec.map (sizeNCC (sucs n)) (c ∷ cs))) ⟩
    suc (Vec.sum (Vec.map (sizeNCC (sucs n)) (c ∷ cs)))
  ≡⟨⟩
    sizeNCC (sucs n) (D NCC.NCC.⟨ c ∷ cs ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

CCC≤NCC : (n : ℕ≥ 2) → SizedCCC F ≤Size SizedNCC F n
CCC≤NCC n = 1 , λ A ncc → LanguageCompiler.compile (NCC→CCC n) ncc , ≅-sym (≅[]→≅ (LanguageCompiler.preserves (NCC→CCC n) ncc)) , Eq.subst (sizeCCC (LanguageCompiler.compile (NCC→CCC n) ncc )≤_) (Eq.sym (ℕ.+-identityʳ (sizeNCC n ncc))) (lemma n ncc)
