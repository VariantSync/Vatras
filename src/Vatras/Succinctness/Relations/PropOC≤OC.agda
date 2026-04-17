open import Vatras.Framework.Definitions using (𝔽; 𝔸; atomSize)

module Vatras.Succinctness.Relations.PropOC≤OC (F : 𝔽) where

import Data.List as List
import Data.List.Properties as List
open import Data.Nat using (_+_; _*_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Size using (Size; ∞)
import Relation.Binary.PropositionalEquality as Eq

import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (≅[]→≅)
open import Vatras.Data.Prop using (var)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Succinctness.Sizes using (sizeProp; SizedWFOC; sizeOC; sizeWFOC; SizedWFPropOC; sizePropOC; sizeWFPropOC)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≤ₛ_)
import Vatras.Lang.All
open Vatras.Lang.All.OC using (OC; WFOC; Root; _-<_>-; _❲_❳)
open import Vatras.Translation.Lang.OC-to-PropOC F using (translate; translate'; translate-preserves)

prop-oc≤oc : ∀ {i : Size} {A : 𝔸} (oc : OC F i A) → sizePropOC (translate' oc) ≤ 2 * sizeOC oc
prop-oc≤oc {A = A} (a -< cs >-) =
  begin
    sizePropOC (translate' (a -< cs >-))
  ≡⟨⟩
    1 + (atomSize A a + List.sum (List.map sizePropOC (List.map translate' cs)))
  ≡⟨ Eq.cong (λ x → 1 + (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
    1 + (atomSize A a + List.sum (List.map (sizePropOC ∘ translate') cs))
  ≤⟨ ℕ.+-monoʳ-≤ 1 (ℕ.+-monoʳ-≤ (atomSize A a) (List.sum-map-≤ (sizePropOC ∘ translate') ((2 *_) ∘ sizeOC) cs prop-oc≤oc)) ⟩
    1 + (atomSize A a + List.sum (List.map ((2 *_) ∘ sizeOC) cs))
  ≡⟨ Eq.cong (λ x → 1 + (atomSize A a + List.sum x)) (List.map-∘ cs) ⟩
    1 + (atomSize A a + List.sum (List.map (2 *_) (List.map sizeOC cs)))
  ≡⟨ Eq.cong (λ x → 1 + (atomSize A a + x)) (List.sum-* 2 (List.map sizeOC cs)) ⟩
    1 + (atomSize A a + 2 * List.sum (List.map sizeOC cs))
  ≡⟨ Eq.cong (λ x → 1 + (x + 2 * List.sum (List.map sizeOC cs))) (ℕ.*-identityˡ (atomSize A a)) ⟨
    1 + (1 * atomSize A a + 2 * List.sum (List.map sizeOC cs))
  ≤⟨ ℕ.+-monoʳ-≤ 1 (ℕ.+-monoˡ-≤ (2 * List.sum (List.map sizeOC cs)) (ℕ.*-monoˡ-≤ (atomSize A a) (s≤s (z≤n {1})))) ⟩
    1 + (2 * atomSize A a + 2 * List.sum (List.map sizeOC cs))
  ≤⟨ ℕ.+-monoˡ-≤ (2 * atomSize A a + 2 * List.sum (List.map sizeOC cs)) (s≤s (z≤n {1})) ⟩
    2 + (2 * atomSize A a + 2 * List.sum (List.map sizeOC cs))
  ≡⟨ Eq.cong (2 +_) (ℕ.*-distribˡ-+ 2 (atomSize A a) (List.sum (List.map sizeOC cs))) ⟨
    2 + 2 * (atomSize A a + List.sum (List.map sizeOC cs))
  ≡⟨ ℕ.*-distribˡ-+ 2 1 (atomSize A a + List.sum (List.map sizeOC cs)) ⟨
    2 * (1 + (atomSize A a + List.sum (List.map sizeOC cs)))
  ≡⟨⟩
    2 * sizeOC (a -< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
prop-oc≤oc (prop ❲ c ❳) =
  begin
    sizePropOC (translate' (prop ❲ c ❳))
  ≡⟨⟩
    1 + (sizeProp (var prop) + sizePropOC (translate' c))
  ≡⟨⟩
    2 + sizePropOC (translate' c)
  ≤⟨ ℕ.+-monoʳ-≤ 2 (prop-oc≤oc c) ⟩
    2 + 2 * sizeOC c
  ≡⟨ ℕ.*-distribˡ-+ 2 1 (sizeOC c) ⟨
    2 * (1 + sizeOC c)
  ≡⟨⟩
    2 * sizeOC (prop ❲ c ❳)
  ∎
  where
  open ℕ.≤-Reasoning

wf-prop-oc≤wf-oc : ∀ {i : Size} {A : 𝔸} (oc : WFOC F i A) → sizeWFPropOC (translate oc) ≤ 2 * sizeWFOC oc
wf-prop-oc≤wf-oc {A = A} (Root a cs) =
  begin
    sizeWFPropOC (translate (Root a cs))
  ≡⟨⟩
    1 + (atomSize A a + List.sum (List.map sizePropOC (List.map translate' cs)))
  ≡⟨⟩
    sizePropOC (translate' (a -< cs >-))
  ≤⟨ prop-oc≤oc (a -< cs >-) ⟩
    2 * sizeOC (a -< cs >-)
  ≡⟨⟩
    2 * (1 + (atomSize A a + List.sum (List.map sizeOC cs)))
  ≡⟨⟩
    2 * sizeWFOC (Root a cs)
  ∎
  where
  open ℕ.≤-Reasoning

WFPropOC≤ₛWFOC : SizedWFPropOC F ≤ₛ SizedWFOC F
WFPropOC≤ₛWFOC = 2 , λ A oc oc-translatable → translate oc , ≅[]→≅ (translate-preserves oc) , wf-prop-oc≤wf-oc oc
