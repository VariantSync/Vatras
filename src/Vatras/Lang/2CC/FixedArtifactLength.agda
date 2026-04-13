{-|
This module shows that artifacts of choice calculus expressions have a fixed number of children.
Afterwards, we introduce some more usable lemmas on top og this insight.
-}
open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.2CC.FixedArtifactLength (Dimension : 𝔽) (A : 𝔸) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.List.Relation.Ternary.Interleaving.Propositional using (Interleaving; []; consˡ; consʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Nat as ℕ using (ℕ; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s; _≥_)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; _≢_)
open import Size using (Size; ∞)

import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (_∈_; _⊆_)
open import Vatras.Framework.Variants using (Rose; children-equality)
open import Vatras.Lang.2CC Dimension using (2CC; _⟨_,_⟩; _-<_>-; ⟦_⟧)
open import Vatras.Lang.2CC.ReflectsVariantSize using (reflectsVariantSize)
open import Vatras.Succinctness.Sizes using (sizeRose; size2CC)

_≉_ : Rose ∞ A → Rose ∞ A → Set
(a₁ Rose.-< cs₁ >-) ≉ (a₂ Rose.-< cs₂ >-) = List.length cs₁ ≢ List.length cs₂

{-|
The key insight of this module:
Given a choice calculus expression with an artifact at the root,
all expressed variants must have the same number of children.
-}
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

{-|
We can partition a list of variants
on whether we can choose the left or right alternative of a choice
in order to configure each variant.
-}
partition : ∀ {i : Size}
  → (D : Dimension) (c₁ c₂ : 2CC i A)
  → (vs : List (Rose ∞ A))
  → AllPairs _≉_ vs
  → All (_∈ ⟦ D 2CC.⟨ c₁ , c₂ ⟩ ⟧) vs
  → ∃[ vs₁ ] ∃[ vs₂ ]
    Interleaving vs₁ vs₂ vs
  × All (_∈ ⟦ c₁ ⟧) vs₁
  × All (_∈ ⟦ c₂ ⟧) vs₂
partition D c₁ c₂ [] unique-vs vs⊆e = [] , [] , [] , [] , []
partition D c₁ c₂ (v ∷ vs) (v∉vs ∷ unique-vs) ((c , v≡e) ∷ vs⊆e)
  with partition D c₁ c₂ vs unique-vs vs⊆e
... | vs₁ , vs₂ , partition , vs₁⊆e , vs₂⊆e
  with c D
... | true = v ∷ vs₁ , vs₂ , consˡ partition , (c , v≡e) ∷ vs₁⊆e , vs₂⊆e
... | false = vs₁ , v ∷ vs₂ , consʳ partition , vs₁⊆e , (c , v≡e) ∷ vs₂⊆e

{-|
Gives a lower bound on the size of a choice calculus expression
given that it expresses a number of variants with pairwise different child count.
-}
sum≤size2CC : ∀ {i : Size}
  → (e : 2CC i A)
  → (vs : List (Rose ∞ A))
  → AllPairs (_≉_) vs
  → All (_∈ ⟦ e ⟧) vs
  → List.sum (List.map sizeRose vs) ≤ size2CC e
sum≤size2CC (a -< cs >-) [] unique-vs vs⊆e = z≤n
sum≤size2CC (a -< cs >-) (v ∷ []) unique-vs (v∈e ∷ []) =
  begin
    List.sum (List.map sizeRose (v ∷ []))
  ≡⟨⟩
    sizeRose v + 0
  ≡⟨ ℕ.+-identityʳ (sizeRose v) ⟩
    sizeRose v
  ≤⟨ reflectsVariantSize v (a -< cs >-) v∈e ⟩
    size2CC (a -< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
sum≤size2CC (a -< cs >-) ((a₁ Rose.-< cs₁ >-) ∷ (a₂ Rose.-< cs₂ >-) ∷ vs) ((v₁≢v₂ ∷ v₁∉vs) ∷ unique-vs) (v₁∈e ∷ v₂∈e ∷ vs⊆e) =
  ⊥-elim (v₁≢v₂ (Eq.trans (fixedChildCount v₁∈e) (Eq.sym (fixedChildCount v₂∈e))))
sum≤size2CC (D ⟨ c₁ , c₂ ⟩) vs unique-vs vs⊆e with partition D c₁ c₂ vs unique-vs vs⊆e
... | vs₁ , vs₂ , partition , vs₁⊆c₁ , vs₂⊆c₂ =
  begin
    List.sum (List.map sizeRose vs)
  ≡⟨ List.sum-Interleaving (List.map-Interleaving partition) ⟨
    List.sum (List.map sizeRose vs₁) + List.sum (List.map sizeRose vs₂)
  ≤⟨ ℕ.+-mono-≤ (sum≤size2CC c₁ vs₁ (List.AllPairs-resp-⊆ (List.Interleaving⇒Sublistˡ partition) unique-vs) vs₁⊆c₁) (sum≤size2CC c₂ vs₂ (List.AllPairs-resp-⊆ (List.Interleaving⇒Sublistʳ partition) unique-vs) vs₂⊆c₂) ⟩
    size2CC c₁ + size2CC c₂
  <⟨ ℕ.n<1+n (size2CC c₁ + size2CC c₂) ⟩
    size2CC (D ⟨ c₁ , c₂ ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

{-|
Gives a lower bound on the size of a choice calculus expression
given that it expresses a number of variants with pairwise different child count.
In contrast to `sum≤size2CC`, this lemma is a simplified special case
which makes use of a lower bound on the variant size.
-}
different-children-counts :
  ∀ {i : Size}
  → (n : ℕ)
  → (e : 2CC i A)
  → (vs : List (Rose ∞ A))
  → All (_∈ ⟦ e ⟧) vs
  → All (λ v → sizeRose v ≥ n) vs
  → AllPairs _≉_ vs
  → size2CC e ≥ List.length vs * n
different-children-counts n e vs vs⊆e vs≥n unique-vs =
  begin
    List.length vs * n
  ≡⟨ List.sum-replicate (List.length vs) n ⟨
    List.sum (List.replicate (List.length vs) n)
  ≡⟨ Eq.cong List.sum (List.map-const n vs) ⟨
    List.sum (List.map (const n) vs)
  ≤⟨ List.sum-map-≤-with∈ vs (λ v v∈vs → All.lookup vs≥n v∈vs) ⟩
    List.sum (List.map sizeRose vs)
  ≤⟨ sum≤size2CC e vs unique-vs (vs⊆e) ⟩
    size2CC e
  ∎
  where
  open ℕ.≤-Reasoning
