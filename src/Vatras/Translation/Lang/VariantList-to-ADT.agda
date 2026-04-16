open import Vatras.Framework.Definitions using (𝔸; 𝕍)
module Vatras.Translation.Lang.VariantList-to-ADT (V : 𝕍) where

open import Data.Bool as Bool using (if_then_else_; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_; _≤_; s≤s; z≤n; _∸_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-refl; n∸n≡0; m≤n⇒m≤1+n; +-∸-assoc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

open import Vatras.Data.EqIndexedSet
open import Vatras.Util.List using (find-or-last)
open import Vatras.Util.AuxProofs using (≡ᵇ-refl; m+n≢ᵇn)

open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Proof.ForFree V using (completeness-by-expressiveness)
open import Vatras.Framework.Properties.Completeness V using (Complete)
open import Vatras.Framework.Relation.Expressiveness V using (_≽_; expressiveness-from-compiler)

open import Vatras.Lang.VariantList V as VariantList using (VariantList; VariantListL)
open import Vatras.Lang.VariantList.Properties V using (VariantList-is-Complete)
open import Vatras.Lang.ADT ℕ V

{-|
This function encodes a non-empty list of forests into a rootless variation tree.
This encoding produces n-1 choices where n is the number of forests to encode.

Arguments:
1. Next available index for new feature names.
2. Head of list of forests to encode
3. Tail of list of forests to encode
-}
translate' : ∀ {A} → ℕ → V A → List (V A) → ADT A
translate' n x []       = leaf x
translate' n x (y ∷ ys) = n ⟨ leaf x , translate' (suc n) y ys ⟩

translate : ∀ {A} → VariantList A → ADT A
translate (x ∷ xs) = translate' zero x xs

{-|
A variation tree created by "translate" from a list l produces a forest
from the list at index i when exactly the feature i is set to true.
-}
conf : ℕ → Configuration
conf = _≡ᵇ_

{-|
From a configuration, we can compute the index of the produced variant in the initial list.
To do so, we have to inspect the feature at each choice from 0 up to "max", where "max" is the
index of the feature in the last choice.
To prove termination, we start with index i = max (see fnoc) and decrease i step by step.
To inspect the features in ascending order though, we hence have to inspect the configuration c at point "max - i" at each step.
The "offset" value is needed for induction to specify at which point in a sublist we are currently at (i.e., how far we recursed).
-}
fnoci : (offset max i : ℕ) → Configuration → ℕ
fnoci offset max zero c = max
fnoci offset max (suc i) c =
  if c (offset + (max ∸ suc i))
  then max ∸ suc i
  else fnoci offset max i c

fnoc : (max : ℕ) → Configuration → ℕ
fnoc max = fnoci zero max max

{-|
The values for "max" and "offset" balance out.
-}
fnoci-invariant : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : List⁺ A) (n m i : ℕ) (c : Configuration) →
    i ≤ m →
    find-or-last (fnoci (suc n)      m  i c) (     xs)
  ≡ find-or-last (fnoci      n  (suc m) i c) (x ∷⁺ xs)
fnoci-invariant x xs n m zero c z≤n = refl
fnoci-invariant x xs n (suc m) (suc i) c (s≤s i≤m)
  rewrite +-∸-assoc 1 i≤m
        | sym (+-suc n (m ∸ i))
        with c (n + suc (m ∸ i))
... | true  = refl
... | false = fnoci-invariant x xs n (suc m) i c (m≤n⇒m≤1+n i≤m)

module Preservation (A : 𝔸) where
  translate'-preserves-conf : ∀ (x : V A) (xs : List (V A)) (n : ℕ) (i : ℕ) →
    ⟦ translate' n x xs ⟧ (conf (i + n)) ≡ VariantList.⟦ x ∷ xs ⟧ i
  translate'-preserves-conf x [] n i = refl
  translate'-preserves-conf x (y ∷ ys) n zero    rewrite ≡ᵇ-refl n = refl
  translate'-preserves-conf x (y ∷ ys) n (suc i) rewrite m+n≢ᵇn i n =
    begin
      ⟦ translate' (suc n) y ys ⟧ (conf (suc i + n))
    ≡⟨ cong (λ eq → ⟦ translate' (suc n) y ys ⟧ (conf eq)) (+-suc i n) ⟨
      ⟦ translate' (suc n) y ys ⟧ (conf (i + suc n))
    ≡⟨ translate'-preserves-conf y ys (suc n) i ⟩
      VariantList.⟦ y ∷ ys ⟧ i
    ≡⟨⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧ (suc i)
    ∎

  preserves-⊆ : ∀ (l : VariantList A)
    → VariantList.⟦ l ⟧ ⊆[ conf ] ⟦ translate l ⟧
  preserves-⊆ (x ∷ xs) i =
    begin
      VariantList.⟦ x ∷ xs ⟧ i
    ≡⟨ translate'-preserves-conf x xs zero i ⟨
      ⟦ translate' zero x xs ⟧ (conf (i + zero))
    ≡⟨ cong (λ eq → ⟦ translate' zero x xs ⟧ (conf eq)) (+-identityʳ i) ⟩
      ⟦ translate' zero x xs ⟧ (conf i)
    ≡⟨⟩
      ⟦ translate (x ∷ xs) ⟧ (conf i)
    ∎

  translate'-preserves-fnoc : ∀ (x : V A) (xs : List (V A)) (n : ℕ) (c : Configuration) →
      ⟦ translate' n x xs ⟧ c
    ≡ VariantList.⟦ x ∷ xs ⟧ (fnoci n (List⁺.length (x ∷ xs)) (List⁺.length (x ∷ xs)) c)
  translate'-preserves-fnoc x [] n c = refl
  translate'-preserves-fnoc x (y ∷ ys) n c with c n in eq
  ... | true  rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq = refl
  ... | false rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq =
    begin
      ⟦ translate' (suc n) y ys ⟧ c
    ≡⟨ translate'-preserves-fnoc y ys (suc n) c ⟩
      VariantList.⟦     y ∷ ys ⟧
        (fnoci (suc n) (List⁺.length (    y ∷ ys)) (List⁺.length (y ∷ ys)) c)
    ≡⟨ fnoci-invariant x (y ∷ ys) n (List⁺.length (y ∷ ys)) (List⁺.length (y ∷ ys)) c ≤-refl ⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧
        (fnoci n       (List⁺.length (x ∷ y ∷ ys)) (List⁺.length (y ∷ ys)) c)
    ∎

  preserves-⊇ : ∀ (l : VariantList A)
    → ⟦ translate l ⟧ ⊆[ fnoc (List⁺.length l) ] VariantList.⟦ l ⟧
  preserves-⊇ (x ∷ xs) c =
    begin
      ⟦ translate (x ∷ xs) ⟧ c
    ≡⟨⟩
      ⟦ translate' zero x xs ⟧ c
    ≡⟨ translate'-preserves-fnoc x xs zero c ⟩
      VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) c)
    ∎

VariantList→ADT : LanguageCompiler VariantListL ADTL
VariantList→ADT = record
  { compile = translate
  ; config-compiler = λ e → record { to = conf ; from = fnoc (List⁺.length e) }
  ; preserves = λ {A} e →
    let open Preservation A in
      preserves-⊆ e , preserves-⊇ e
  }

ADT≽VariantList : ADTL ≽ VariantListL
ADT≽VariantList = expressiveness-from-compiler VariantList→ADT

ADT-is-complete : Complete ADTL
ADT-is-complete = completeness-by-expressiveness VariantList-is-Complete ADT≽VariantList
