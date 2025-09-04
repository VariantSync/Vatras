open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.2CC.FixedArtifactLength (Dimension : 𝔽) (A : 𝔸) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; []; _∷_; concatMap; _++_)
import Data.List.Properties as List
open import Data.List.Relation.Ternary.Interleaving.Propositional using (Interleaving; []; consˡ; consʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Nat as ℕ using (ℕ; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; _≢_)
open import Size using (Size; ∞)

import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (_∈_)
open import Vatras.Framework.Variants using (Rose; children-equality)
open import Vatras.Lang.2CC Dimension using (2CC; _⟨_,_⟩; _-<_>-; ⟦_⟧)
open import Vatras.Lang.2CC.ReflectsVariantSize using (reflectsVariantSize)
open import Vatras.Succinctness.Sizes Dimension using (sizeRose; size2CC)

_≉_ : Rose ∞ A → Rose ∞ A → Set
(a₁ Rose.-< cs₁ >-) ≉ (a₂ Rose.-< cs₂ >-) = List.length cs₁ ≢ List.length cs₂

fixedChildCount : ∀ {i}
  → {a₁ : atoms A} {cs₁ : List (Rose ∞ A)}
  → {a₂ : atoms A} {cs₂ : List (2CC i A)}
  → (a₁ Rose.-< cs₁ >-) ∈ ⟦ a₂ -< cs₂ >- ⟧
  → List.length cs₁ ≡ List.length cs₂
fixedChildCount {cs₁ = cs₁} {cs₂ = cs₂} (c , v≡e) =
    List.length cs₁
  ≡⟨ Eq.cong List.length (children-equality v≡e) ⟩
    List.length (List.map (λ e → ⟦ e ⟧ c) cs₂)
  ≡⟨ List.length-map (λ e → ⟦ e ⟧ c) cs₂ ⟩
    List.length cs₂
  ∎
  where
  open Eq.≡-Reasoning

partition : ∀ {i : Size} {ℓ} {I : Set ℓ}
  → (D : Dimension) (c₁ c₂ : 2CC i A)
  → (is : List I)
  → (f : I → Rose ∞ A)
  → AllPairs (λ i j → f i ≉ f j) is
  → All (λ i → f i ∈ ⟦ D 2CC.⟨ c₁ , c₂ ⟩ ⟧) is
  → ∃[ is₁ ] ∃[ is₂ ]
    Interleaving is₁ is₂ is
  × All (λ i → f i ∈ ⟦ c₁ ⟧) is₁
  × All (λ i → f i ∈ ⟦ c₂ ⟧) is₂
partition D c₁ c₂ [] f unique-vs vs⊆e = [] , [] , [] , [] , []
partition D c₁ c₂ (i ∷ is) f (v∉vs ∷ unique-vs) ((c , v≡e) ∷ vs⊆e)
  with partition D c₁ c₂ is f unique-vs vs⊆e
... | is₁ , is₂ , partition , vs₁⊆e , vs₂⊆e
  with c D
... | true = i ∷ is₁ , is₂ , consˡ partition , (c , v≡e) ∷ vs₁⊆e , vs₂⊆e
... | false = is₁ , i ∷ is₂ , consʳ partition , vs₁⊆e , (c , v≡e) ∷ vs₂⊆e

sum≤size2CC : ∀ {i : Size} {ℓ} {I : Set ℓ}
  → (e : 2CC i A)
  → (is : List I)
  → (f : I → Rose ∞ A)
  → AllPairs (λ i j → f i ≉ f j) is
  → All (λ i → f i ∈ ⟦ e ⟧) is
  → List.sum (List.map (sizeRose ∘ f) is) ≤ size2CC e
sum≤size2CC (a -< cs >-) [] f unique-vs vs⊆e = z≤n
sum≤size2CC (a -< cs >-) (i₁ ∷ []) f unique-vs (v∈e ∷ []) =
  begin
    List.sum (List.map (sizeRose ∘ f) (i₁ ∷ []))
  ≡⟨⟩
    sizeRose (f i₁) + 0
  ≡⟨ ℕ.+-identityʳ (sizeRose (f i₁)) ⟩
    sizeRose (f i₁)
  ≤⟨ reflectsVariantSize (f i₁) (a -< cs >-) v∈e ⟩
    size2CC (a -< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
sum≤size2CC (a -< cs >-) (i₁ ∷ i₂ ∷ is) f ((v₁≢v₂ ∷ v₁∉vs) ∷ unique-vs) (v₁∈e ∷ v₂∈e ∷ vs⊆e) with f i₁ | f i₂
... | a₁ Rose.-< cs₁ >- | a₂ Rose.-< cs₂ >- =
  ⊥-elim (v₁≢v₂ (Eq.trans (fixedChildCount v₁∈e) (Eq.sym (fixedChildCount v₂∈e))))
sum≤size2CC (D ⟨ c₁ , c₂ ⟩) is f unique-vs vs⊆e with partition D c₁ c₂ is f unique-vs vs⊆e
... | is₁ , is₂ , partition , vs₁⊆c₁ , vs₂⊆c₂ =
  begin
    List.sum (List.map (sizeRose ∘ f) is)
  ≡⟨ List.sum-Interleaving partition ⟨
    List.sum (List.map (sizeRose ∘ f) is₁) + List.sum (List.map (sizeRose ∘ f) is₂)
  ≤⟨ ℕ.+-mono-≤ (sum≤size2CC c₁ is₁ f (List.AllPairs-resp-⊆ (List.Interleaving⇒Sublistˡ partition) unique-vs) vs₁⊆c₁) (sum≤size2CC c₂ is₂ f (List.AllPairs-resp-⊆ (List.Interleaving⇒Sublistʳ partition) unique-vs) vs₂⊆c₂) ⟩
    size2CC c₁ + size2CC c₂
  <⟨ ℕ.n<1+n (size2CC c₁ + size2CC c₂) ⟩
    size2CC (D ⟨ c₁ , c₂ ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

unique-lengths⇒m*sizeRose≤size2CC : ∀ {i : Size} (n : ℕ)
  → (2cc : 2CC i A)
  → (ls : List ℕ)
  → (f : ℕ → Rose ∞ A)
  → (∀ (l : ℕ) → n ≤ sizeRose (f l))
  → (∀ {l₁ l₂ : ℕ} → l₁ ≢ l₂ → f l₁ ≉ f l₂)
  → AllPairs _≢_ ls
  → All (λ l → f l ∈ ⟦ 2cc ⟧) ls
  → List.length ls * n ≤ size2CC 2cc
unique-lengths⇒m*sizeRose≤size2CC n 2cc ls f f-size f-≉ unique-ls all-∈ =
  begin
    List.length ls * n
  ≡⟨ List.sum-replicate (List.length ls) n ⟨
    List.sum (List.replicate (List.length ls) n)
  ≡⟨ Eq.cong List.sum (List.map-const n ls) ⟨
    List.sum (List.map (const n) ls)
  ≤⟨ List.sum-map-≤ (const n) (sizeRose ∘ f) ls f-size ⟩
    List.sum (List.map (sizeRose ∘ f) ls)
  ≤⟨ sum≤size2CC 2cc ls f (AllPairs.map f-≉ unique-ls) all-∈ ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning
