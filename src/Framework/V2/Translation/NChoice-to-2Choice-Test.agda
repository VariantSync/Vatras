{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.V2.Definitions
module Framework.V2.Translation.NChoice-to-2Choice-Test (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≡ᵇ_; _≤_; z≤n; s≤s; _<_; _∸_)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_; length; toList) renaming (map to map⁺)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Level using (_⊔_)

open import Framework.V2.Compiler using (ConstructCompiler)

open import Framework.V2.Constructs.Choices as Chc
open Chc.Choice₂ using (_⟨_,_⟩) renaming (Syntax to 2Choice; Standard-Semantics to ⟦_⟧₂; Config to Config₂)
open Chc.Choiceₙ using (_⟨_⟩) renaming (Syntax to NChoice; Standard-Semantics to ⟦_⟧ₙ; Config to Configₙ)
open Chc.VLChoice₂ using () renaming (Construct to C₂)
open Chc.VLChoiceₙ using () renaming (Construct to Cₙ)

open import Framework.V2.Translation.NChoice-to-2Choice {Q = F} as BLUB
module Trans = BLUB.Translate ℕ
open Trans
open IndexedDimension

-- example : ∀ {D : F} → D ⟨ 1 , 2 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , val 2 ⟩) ⟩
-- example = step base

-- example' : ∀ {D : F}
--   → D ⟨ 1 , 2 ∷ 3 ∷ [] ⟩⇝ (D ∙ 0) ⟨ val 1 , chc ((D ∙ 1) ⟨ val 2 , chc ((D ∙ 2) ⟨ val 3 , val 3 ⟩) ⟩) ⟩
-- example' = step (step base)

-- module Pres = Trans.Preservation
-- open Pres

-- open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
-- import Data.IndexedSet
-- module ISN = Data.IndexedSet (Eq.setoid ℕ)
-- open ISN using (_∈_at_; _⊆[_]_; _≅[_][_]_)

-- Conf : ∀ {ℓ} (Q : Set ℓ) → Set ℓ
-- Conf Q = Configₙ Q → Config₂ (IndexedDimension Q)

-- Fnoc : ∀ {ℓ₁ ℓ₂} (Q : Set ℓ₁) (A : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
-- Fnoc Q A = NChoice Q A → Config₂ (IndexedDimension Q) → Configₙ Q

-- un-conf : ∀ {ℓ} {Q : Set ℓ} → Conf Q
-- un-conf cₙ (D ∙ i) = true

-- un-fnoc : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Fnoc Q A
-- un-fnoc _ c₂ D = 0

-- un : ∀ {D : F} → Preserved (D ⟨ 1 ∷ [] ⟩) un-conf (un-fnoc (D ⟨ 1 ∷ [] ⟩))
-- proj₁ (un {D}) c with c D in eq
-- ... | zero = refl
-- ... | suc x = refl
-- proj₂ (un {D}) c with c (D ∙ 0) in eq
-- ... | false = refl
-- ... | true = refl

-- bi-conf : ∀ {ℓ} {Q : Set ℓ} → Conf Q
-- bi-conf cₙ (D ∙ i) with cₙ D
-- ... | zero = true
-- ... | suc x = false

-- bi-fnoc : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Fnoc Q A
-- bi-fnoc _ c₂ D with c₂ (D ∙ 0)
-- ... | false = 1
-- ... | true = 0

-- bi : ∀ {D : F} → Preserved (D ⟨ 1 ∷ 2 ∷ [] ⟩) bi-conf (bi-fnoc (D ⟨ 1 ∷ 2 ∷ [] ⟩))
-- proj₁ (bi {D}) c with c D
-- ... | zero = refl
-- ... | suc x with bi-conf c (D ∙ 1)
-- ...         | false = refl
-- ...         | true  = refl
-- proj₂ (bi {D}) c with c (D ∙ 0)
-- ... | true = refl
-- ... | false with c (D ∙ 1)
-- ...         | false = refl
-- ...         | true  = refl

-- open import Relation.Nullary.Negation using (¬_)
-- open import Relation.Nullary.Reflects using (ofⁿ; ofʸ)
-- open import Relation.Nullary.Decidable using (_because_; does)

-- tri-conf : ∀ {ℓ} {Q : Set ℓ} → Conf Q
-- tri-conf cₙ (D ∙ i) = cₙ D ≡ᵇ i

-- -- correct : ∀ (c : 2Config) (i : ℕ)
-- --   → c (D ∙ i) ≡ true
-- --   → (∀ (j : ℕ) → j < i → c (D ∙ j) ≡ false)
-- --   → (fnoc c) D ≡ i
-- tri-fnoc-find-true : ∀ {ℓ} {Q : Set ℓ} → Config₂ (IndexedDimension Q) → Q → (cur : ℕ) → (max : ℕ) → ℕ
-- tri-fnoc-find-true c₂ D zero max = max
-- tri-fnoc-find-true c₂ D (suc cur) max =
--   let i = max ∸ suc cur in
--   if c₂ (D ∙ i)
--   then i
--   else tri-fnoc-find-true c₂ D cur max

-- -- tri-fnoc-find-true-nice : ∀ {ℓ} {Q : Set ℓ} {c₂ : Config₂ (IndexedDimension Q)} {D : Q}
-- --   → (cur : ℕ) → (max : ℕ)
-- --   → c (max ∸ cur) ≡ true
-- -- tri-fnoc-find-true c₂ D zero max = max

-- tri-fnoc : ∀ {ℓ₁ ℓ₂} {Q : Set ℓ₁} {A : Set ℓ₂} → Fnoc Q A
-- tri-fnoc (_ ⟨ es ⟩) c₂ D = tri-fnoc-find-true c₂ D (length es) (length es)

-- open ConfSpec
-- open FnocSpec
-- open Eq.≡-Reasoning

-- ≡ᵇ-refl : ∀ (x : ℕ) → (x ≡ᵇ x) ≡ true
-- ≡ᵇ-refl zero = refl
-- ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

-- tri-conf-nice : ∀ (D : F) → ConfSpec D tri-conf
-- select-n (tri-conf-nice D) c refl =
--   begin
--     tri-conf c (D ∙ c D)
--   ≡⟨⟩
--     c D ≡ᵇ c D
--   ≡⟨ ≡ᵇ-refl (c D) ⟩
--     true
--   ∎
-- deselect-<n (tri-conf-nice D) c {i} x with c D in eq
-- deselect-<n (tri-conf-nice D) c {i} (s≤s x) | suc y =
--   begin
--     suc y ≡ᵇ i
--   ≡⟨ nono x ⟩
--     false
--   ∎
--   where
--     nono : ∀ {m n} → m ≤ n → (suc n ≡ᵇ m) ≡ false
--     nono z≤n = refl
--     nono (s≤s x) = nono x

-- open import Data.Nat.Properties using (≤-refl; n∸n≡0) --; m∸n≤m; m∸n≢0⇒n<m; 0∸n≡0; n∸n≡0; m≤n⇒m∸n≡0)
-- tri-fnoc-nice : ∀ {ℓ₂} {A : Set ℓ₂} → (D : F) (es : List⁺ A) → FnocSpec D (tri-fnoc (D ⟨ es ⟩))
-- correct (tri-fnoc-nice D es) c₂ zero    cDi≡true <-false rewrite n∸n≡0 (length es) | cDi≡true = refl
-- correct (tri-fnoc-nice D es) c₂ (suc i) cDi≡true <-false rewrite n∸n≡0 (length es) = {!!}

-- tri : ∀ {D : F} → Preserved (D ⟨ 1 ∷ 2 ∷ 3 ∷ [] ⟩) tri-conf (tri-fnoc (D ⟨ 1 ∷ 2 ∷ 3 ∷ [] ⟩))
-- proj₁ (tri {D}) c with tri-conf c (D ∙ 0)
-- ... | true = {!!} -- is true
-- ... | false with tri-conf c (D ∙ 1)
-- ...         | true = {!!} -- is true
-- ...         | false with tri-conf c (D ∙ 2)
-- ...                 | true = {!!} -- true
-- ...                 | false = {!!} -- true
-- proj₂ (tri {D}) c = {!!}
