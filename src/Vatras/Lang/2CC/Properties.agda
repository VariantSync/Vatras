open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; 𝔼; ℂ)
module Vatras.Lang.2CC.Properties {Dimension : 𝔽} {A : 𝔸} where

{-
In the following, we prove some interesting properties about binary choice calculus,
known from the respective papers.
-}

open import Size using (Size; ∞)
open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.List as List
open import Data.Nat using (ℕ)
open import Data.Vec as Vec using (Vec; toList; zipWith)
import Data.Vec.Properties as Vec
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Vatras.Util.Vec as Vec
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_⊢_≣₁_)
open import Vatras.Lang.2CC Dimension using (2CC; _-<_>-; _⟨_,_⟩; 2CCL; ⟦_⟧)

{-|
Given a choice between two artifacts with the same atom 'a',
we can factor out this atom 'a' outside of the choice because no matter
how we configure the choice, the resulting expression will always have 'a'
at the top.
-}
choice-factoring : ∀ {i} {D : Dimension} {a : atoms A} {n : ℕ}
  → (xs ys : Vec (2CC i A) n)
    ------------------------------------------------
  → 2CCL ⊢
        D ⟨ a -< toList xs >- , a -< toList ys >- ⟩
      ≣₁ a -< toList (zipWith (D ⟨_,_⟩) xs ys) >-
choice-factoring {i} {D} {a} {n} xs ys c =
    ⟦ D ⟨ a -< toList xs >- , a -< toList ys >- ⟩ ⟧ c
  ≡⟨⟩
    (if c D then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
  ≡⟨ lemma (c D) ⟩
    a V.-< toList (zipWith (λ x y → if c D then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
  ≡⟨⟩
    a V.-< toList (zipWith (λ x y → ⟦ D ⟨ x , y ⟩ ⟧ c) xs ys) >-
  ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.map-zipWith (λ e → ⟦ e ⟧ c) (D ⟨_,_⟩) xs ys)) ⟨
    a V.-< toList (Vec.map (λ e → ⟦ e ⟧ c) (zipWith (D ⟨_,_⟩) xs ys)) >-
  ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) (zipWith (D ⟨_,_⟩) xs ys)) ⟩
    a V.-< List.map (λ e → ⟦ e ⟧ c) (toList (zipWith (D ⟨_,_⟩) xs ys)) >-
  ≡⟨⟩
    ⟦ a -< toList (zipWith (D ⟨_,_⟩) xs ys) >- ⟧ c
  ∎
  where
    open Eq.≡-Reasoning
    lemma : (b : Bool) →
        (if b then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
      ≡ a V.-< toList (zipWith (λ x y → if b then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
    lemma false =
        (if false then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
      ≡⟨⟩
        ⟦ a -< toList ys >- ⟧ c
      ≡⟨⟩
        a V.-< List.map (λ e → ⟦ e ⟧ c) (toList ys) >-
      ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) ys) ⟨
        a V.-< toList (Vec.map (λ y → ⟦ y ⟧ c) ys) >-
      ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.zipWith₂ (λ y → ⟦ y ⟧ c) xs ys)) ⟨
        a V.-< toList (zipWith (λ x y → ⟦ y ⟧ c) xs ys) >-
      ≡⟨⟩
        a V.-< toList (zipWith (λ x y → if false then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
      ∎
    lemma true =
        (if true then ⟦ a -< toList xs >- ⟧ c else ⟦ a -< toList ys >- ⟧ c)
      ≡⟨⟩
        ⟦ a -< toList xs >- ⟧ c
      ≡⟨⟩
        a V.-< List.map (λ e → ⟦ e ⟧ c) (toList xs) >-
      ≡⟨ Eq.cong (a V.-<_>-) (Vec.toList-map (λ e → ⟦ e ⟧ c) xs) ⟨
        a V.-< toList (Vec.map (λ x → ⟦ x ⟧ c) xs) >-
      ≡⟨ Eq.cong (a V.-<_>-) (Eq.cong toList (Vec.zipWith₁ (λ x → ⟦ x ⟧ c) xs ys)) ⟨
        a V.-< toList (zipWith (λ x y → ⟦ x ⟧ c) xs ys) >-
      ≡⟨⟩
        a V.-< toList (zipWith (λ x y → if true then ⟦ x ⟧ c else ⟦ y ⟧ c) xs ys) >-
      ∎

{-|
A choice between two equal alternatives is no choice.
No matter how we configure the choice, the result stays the same.
-}
choice-idempotency : ∀ {D} {e : 2CC ∞ A}
    ---------------------------------
  → 2CCL ⊢ D ⟨ e , e ⟩ ≣₁ e
choice-idempotency {D} {e} c with c D
... | false = refl
... | true  = refl

{-|
If the left alternative of a choice is semantically equivalent
to another expression l′, we can replace the left alternative with l′.
-}
choice-l-congruence : ∀ {i : Size} {D : Dimension} {l l′ r : 2CC i A}
  → 2CCL ⊢ l ≣₁ l′
    ---------------------------------------
  → 2CCL ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l′ , r ⟩
choice-l-congruence {D = D} l≣l′ c with c D
... | false = refl
... | true  = l≣l′ c

{-|
If the right alternative of a choice is semantically equivalent
to another expression r′, we can replace the right alternative with r′.
-}
choice-r-congruence : ∀ {i : Size} {D : Dimension} {l r r′ : 2CC i A}
  → 2CCL ⊢ r ≣₁ r′
    ---------------------------------------
  → 2CCL ⊢ D ⟨ l , r ⟩ ≣₁ D ⟨ l , r′ ⟩
choice-r-congruence {D = D} r≣r′ c with c D
... | false = r≣r′ c
... | true  = refl
