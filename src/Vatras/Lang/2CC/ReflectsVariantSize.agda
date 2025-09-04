open import Vatras.Framework.Definitions using (𝔽; 𝔸; atomSize)
module Vatras.Lang.2CC.ReflectsVariantSize {Dimension : 𝔽} {A : 𝔸} where

open import Data.Bool using (true; false)
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (suc; _+_; _≤_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (_∈_)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Lang.2CC Dimension using (2CC; _⟨_,_⟩; _-<_>-; ⟦_⟧)
open import Vatras.Succinctness.Sizes Dimension using (sizeRose; size2CC)

reflectsVariantSize : ∀ {i : Size}
  → (v : Rose ∞ A)
  → (e : 2CC i A)
  → v ∈ ⟦ e ⟧
  → sizeRose v ≤ size2CC e
reflectsVariantSize v (D ⟨ l , r ⟩) (config , v≡e) with config D
reflectsVariantSize v (D ⟨ l , r ⟩) (config , v≡e) | true =
  begin
    sizeRose v
  ≤⟨ reflectsVariantSize v l (config , v≡e) ⟩
    size2CC l
  <⟨ ℕ.n<1+n (size2CC l) ⟩
    suc (size2CC l)
  ≤⟨ s≤s (ℕ.m≤m+n (size2CC l) (size2CC r)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning
reflectsVariantSize v (D ⟨ l , r ⟩) (config , v≡e) | false =
  begin
    sizeRose v
  ≤⟨ reflectsVariantSize v r (config , v≡e) ⟩
    size2CC r
  <⟨ ℕ.n<1+n (size2CC r) ⟩
    suc (size2CC r)
  ≤⟨ s≤s (ℕ.m≤n+m (size2CC r) (size2CC l)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning
reflectsVariantSize (a Rose.-< cs >-) (a' -< cs' >-) (config , v≡e) =
  begin
    sizeRose (a Rose.-< cs >-)
  ≡⟨⟩
    suc (atomSize A a + List.sum (List.map sizeRose cs))
  ≤⟨ s≤s (ℕ.+-monoʳ-≤ (atomSize A a) (go cs cs' (proj₂ (Rose-injective v≡e)))) ⟩
    suc (atomSize A a + List.sum (List.map size2CC cs'))
  ≡⟨⟩
    size2CC (a -< cs' >-)
  ≡⟨ Eq.cong (λ x → size2CC (x -< cs' >-)) (proj₁ (Rose-injective v≡e)) ⟩
    size2CC (a' -< cs' >-)
  ∎
  where
  open ℕ.≤-Reasoning

  go : ∀ {i : Size}
    → (cs : List (Rose ∞ A)) (cs' : List (2CC i A))
    → cs ≡ List.map (λ c → ⟦ c ⟧ config) cs'
    → List.sum (List.map sizeRose cs) ≤ List.sum (List.map size2CC cs')
  go [] [] cs≡cs' = ℕ.≤-refl
  go (c ∷ cs) (c' ∷ cs') cs≡cs' =
    ℕ.+-mono-≤
      (reflectsVariantSize c c' (config , List.∷-injectiveˡ cs≡cs'))
      (go cs cs' (List.∷-injectiveʳ cs≡cs'))
