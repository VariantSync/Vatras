module Vatras.Succinctness.Relations.2CC=2CC where

open import Data.Nat as ℕ using (zero; suc; _+_)
import Data.Nat.Properties as ℕ
import Data.List as List
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Data.Vec as Vec using ([]; _∷_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_)
open import Size using (Size; ∞)

open import Vatras.Util.Nat.AtLeast using (sucs)
open import Vatras.Data.EqIndexedSet using (≅[]→≅)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atomSize)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Lang.All
open import Vatras.Translation.Lang.2CC.Rename using (rename) renaming (preserves to rename-preserves)
import Vatras.Translation.Lang.2CC-to-NCC
open Vatras.Translation.Lang.2CC-to-NCC.2Ary using () renaming (translate to 2CC→NCC; preserves to 2CC→NCC-preserves)
import Vatras.Translation.Lang.NCC-to-2CC
open Vatras.Translation.Lang.NCC-to-2CC.2Ary using () renaming (translate to NCC→2CC; preserves to NCC→2CC-preserves)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≤Size_; _=Size_)
open import Vatras.Succinctness.Sizes using (Sized2CC; size2CC; SizedNCC; sizeNCC)

module _ {F₁ F₂ : 𝔽} (f : F₂ → F₁) (f⁻¹ : F₁ → F₂) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) where
  rename-preserves-size2CC : ∀ {i : Size} {A : 𝔸}
    → (e : 2CC.2CC F₂ i A)
    → size2CC (rename f e) ≡ size2CC e
  rename-preserves-size2CC {A = A} (a 2CC.2CC.-< cs >-) =
    begin
      size2CC (rename f (a 2CC.2CC.-< cs >-))
    ≡⟨⟩
      size2CC (a 2CC.2CC.-< List.map (rename f) cs >-)
    ≡⟨⟩
      suc (atomSize A a + List.sum (List.map size2CC (List.map (rename f) cs)))
    ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
      suc (atomSize A a + List.sum (List.map (size2CC ∘ rename f) cs))
    ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-cong rename-preserves-size2CC cs) ⟩
      suc (atomSize A a + List.sum (List.map size2CC cs))
    ≡⟨⟩
      size2CC (a 2CC.2CC.-< cs >-)
    ∎
    where
    open Eq.≡-Reasoning
  rename-preserves-size2CC (D 2CC.2CC.⟨ l , r ⟩) =
    begin
      size2CC (rename f (D 2CC.2CC.⟨ l , r ⟩))
    ≡⟨⟩
      suc (size2CC (rename f l) + size2CC (rename f r))
    ≡⟨ Eq.cong suc (Eq.cong₂ _+_ (rename-preserves-size2CC l) (rename-preserves-size2CC r)) ⟩
      suc (size2CC l + size2CC r)
    ≡⟨⟩
      size2CC (D 2CC.2CC.⟨ l , r ⟩)
    ∎
    where
    open Eq.≡-Reasoning

  2CC≤2CC : Sized2CC F₁ ≤Size Sized2CC F₂
  2CC≤2CC = 1 , λ A e →
      rename f e
    , ≅[]→≅ (rename-preserves f f⁻¹ f⁻¹∘f≗id e)
    , ℕ.≤-reflexive (Eq.trans (rename-preserves-size2CC e) (Eq.sym (ℕ.+-identityʳ (size2CC e))))

2CC=2CC : ∀ {F₁ F₂ : 𝔽}
  → (f : F₂ → F₁)
  → (f⁻¹ : F₁ → F₂)
  → f⁻¹ ∘ f ≗ id
  → f ∘ f⁻¹ ≗ id
  → Sized2CC F₁ =Size Sized2CC F₂
2CC=2CC f f⁻¹ f⁻¹∘f≗id f∘f⁻¹≗id = 2CC≤2CC f f⁻¹ f⁻¹∘f≗id , 2CC≤2CC f⁻¹ f f∘f⁻¹≗id

2CC→NCC-preserves-size : ∀ {i : Size} {A : 𝔸} {F : 𝔽}
  → (e : 2CC.2CC F i A)
  → sizeNCC (sucs zero) (2CC→NCC e) ≡ size2CC e
2CC→NCC-preserves-size {A = A} {F = F} (a 2CC.2CC.-< cs >-) =
  begin
    sizeNCC (sucs zero) (2CC→NCC (a 2CC.2CC.-< cs >-))
  ≡⟨⟩
    sizeNCC (sucs zero) (a NCC.NCC.-< List.map 2CC→NCC cs >-)
  ≡⟨⟩
    suc (atomSize A a + List.sum (List.map (sizeNCC (sucs zero)) (List.map 2CC→NCC cs)))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
    suc (atomSize A a + List.sum (List.map (sizeNCC (sucs zero) ∘ 2CC→NCC) cs))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-cong 2CC→NCC-preserves-size cs) ⟩
    suc (atomSize A a + List.sum (List.map size2CC cs))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< cs >-)
  ∎
  where
  open Eq.≡-Reasoning
2CC→NCC-preserves-size {F = F} (D 2CC.2CC.⟨ l , r ⟩) =
  begin
    sizeNCC (sucs zero) (2CC→NCC (D 2CC.2CC.⟨ l , r ⟩))
  ≡⟨⟩
    sizeNCC (sucs zero) (D NCC.NCC.⟨ 2CC→NCC l ∷ 2CC→NCC r ∷ [] ⟩)
  ≡⟨⟩
    suc (Vec.sum (Vec.map (sizeNCC (sucs zero)) (2CC→NCC l ∷ 2CC→NCC r ∷ [])))
  ≡⟨⟩
    suc (sizeNCC (sucs zero) (2CC→NCC l) + (sizeNCC (sucs zero) (2CC→NCC r) + 0))
  ≡⟨ Eq.cong (λ x → suc (sizeNCC (sucs zero) (2CC→NCC l) + x)) (ℕ.+-identityʳ (sizeNCC (sucs zero) (2CC→NCC r))) ⟩
    suc (sizeNCC (sucs zero) (2CC→NCC l) + sizeNCC (sucs zero) (2CC→NCC r))
  ≡⟨ Eq.cong suc (Eq.cong₂ _+_ (2CC→NCC-preserves-size l) (2CC→NCC-preserves-size r)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open Eq.≡-Reasoning

NCC→2CC-preserves-size : ∀ {i : Size} {A : 𝔸} {F : 𝔽}
  → (e : NCC.NCC F (sucs zero) i A)
  → size2CC (NCC→2CC e) ≡ sizeNCC (sucs zero) e
NCC→2CC-preserves-size {A = A} {F = F} (a NCC.NCC.-< cs >-) =
  begin
    size2CC (NCC→2CC (a NCC.NCC.-< cs >-))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< List.map NCC→2CC cs >-)
  ≡⟨⟩
    suc (atomSize A a + List.sum (List.map size2CC (List.map NCC→2CC cs)))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
    suc (atomSize A a + List.sum (List.map (size2CC ∘ NCC→2CC) cs))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-cong NCC→2CC-preserves-size cs) ⟩
    suc (atomSize A a + List.sum (List.map (sizeNCC (sucs zero)) cs))
  ≡⟨⟩
    sizeNCC (sucs zero) (a NCC.NCC.-< cs >-)
  ∎
  where
  open Eq.≡-Reasoning
NCC→2CC-preserves-size {F = F} (D NCC.NCC.⟨ c₁ ∷ c₂ ∷ [] ⟩) =
  begin
    size2CC (NCC→2CC (D NCC.NCC.⟨ c₁ ∷ c₂ ∷ [] ⟩))
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ NCC→2CC c₁ , NCC→2CC c₂ ⟩)
  ≡⟨⟩
    suc (size2CC (NCC→2CC c₁) + size2CC (NCC→2CC c₂))
  ≡⟨ Eq.cong suc (Eq.cong₂ _+_ (NCC→2CC-preserves-size c₁) (NCC→2CC-preserves-size c₂)) ⟩
    suc (sizeNCC (sucs zero) c₁ + sizeNCC (sucs zero) c₂)
  ≡⟨ Eq.cong (λ x → suc (sizeNCC (sucs zero) c₁) + x) (ℕ.+-identityʳ (sizeNCC (sucs zero) c₂)) ⟨
    suc (sizeNCC (sucs zero) c₁ + (sizeNCC (sucs zero) c₂ + 0))
  ≡⟨⟩
    suc (Vec.sum (Vec.map (sizeNCC (sucs zero)) (c₁ ∷ c₂ ∷ [])))
  ≡⟨⟩
    sizeNCC (sucs zero) (D NCC.NCC.⟨ c₁ ∷ c₂ ∷ [] ⟩)
  ∎
  where
  open Eq.≡-Reasoning

NCC=2CC : ∀ {F : 𝔽}
  → SizedNCC F (sucs zero) =Size Sized2CC F
NCC=2CC {F} =
    (1 , λ A e → 2CC→NCC e , ≅[]→≅ (2CC→NCC-preserves e) , ℕ.≤-reflexive (Eq.trans (2CC→NCC-preserves-size e) (Eq.sym (ℕ.+-identityʳ (size2CC e)))))
  , (1 , λ A e → NCC→2CC e , ≅[]→≅ (NCC→2CC-preserves e) , ℕ.≤-reflexive (Eq.trans (NCC→2CC-preserves-size e) (Eq.sym (ℕ.+-identityʳ (sizeNCC (sucs zero) e)))))
