open import Vatras.Framework.Definitions using (𝔽; 𝔸)
-- We assume the existence of at least one atom.
module Vatras.Translation.Lang.VariantList-to-VT (F : 𝔽) (f : F) where

open import Data.Bool as Bool using (if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_; _≤_; s≤s; z≤n; _∸_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-refl; n∸n≡0; m≤n⇒m≤1+n; +-∸-assoc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

open import Vatras.Data.Prop using (var)
open import Vatras.Data.EqIndexedSet
open import Vatras.Util.List using (find-or-last)
open import Vatras.Util.AuxProofs using (≡ᵇ-refl; m+n≢ᵇn)

open import Vatras.Framework.Variants using (Forest; encode-idemp)
open import Vatras.Framework.Annotation.IndexedDimension using (Indexed)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Proof.ForFree Forest using (completeness-by-expressiveness)
open import Vatras.Framework.Properties.Completeness Forest using (Complete)
open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_; expressiveness-from-compiler)

open import Vatras.Lang.VariantList Forest as VariantList using (VariantList; VariantListL)
open import Vatras.Lang.VariantList.Properties Forest using (VariantList-is-Complete)
open import Vatras.Lang.VT (Indexed F)
open import Vatras.Lang.VT.Encode (Indexed F)

{-|
This function encodes a non-empty list of forests into a rootless variation tree.
This encoding produces n-1 choices where n is the number of forests to encode.

Arguments:
1. Next available index for new feature names.
2. Head of list of forests to encode
3. Tail of list of forests to encode
-}
translate' : ∀ {A} → ℕ → Forest A → List (Forest A) → List (UnrootedVT A)
translate' n x []       = encode-forest x
translate' n x (y ∷ ys) =
  if[ var (f , n) ]then[
    encode-forest x
  ]else[
    translate' (suc n) y ys
  ] ∷ []

translate : ∀ {A} → VariantList A → VT A
translate (x ∷ xs) = if-true[ translate' zero x xs ]

{-|
A variation tree created by "translate" from a list l produces a forest
from the list at index i when exactly the feature (f , i) is set to true.
-}
conf : ℕ → Configuration
conf i (_ , j) = i ≡ᵇ j

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
  if c (f , offset + (max ∸ suc i))
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
        with c (f , n + suc (m ∸ i))
... | true  = refl
... | false = fnoci-invariant x xs n (suc m) i c (m≤n⇒m≤1+n i≤m)

module Preservation (A : 𝔸) where
  translate'-preserves-conf : ∀ (x : Forest A) (xs : List (Forest A)) (n : ℕ) (i : ℕ) →
    configure-all (conf (i + n)) (translate' n x xs) ≡ VariantList.⟦ x ∷ xs ⟧ i
  translate'-preserves-conf x [] n i =
    begin
      configure-all (conf (i + n)) (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder (conf (i + n)) x ⟩
      x
    ≡⟨⟩
      VariantList.⟦ x ∷ [] ⟧ i
    ∎
  translate'-preserves-conf x (y ∷ ys) n zero rewrite ≡ᵇ-refl n =
    begin
      configure-all (conf n) (encode-forest x) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all (conf n) (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder (conf n) x ⟩
      x
    ≡⟨⟩
      VariantList.⟦ x ∷ y ∷ ys ⟧ zero
    ∎
  translate'-preserves-conf x (y ∷ ys) n (suc i) rewrite m+n≢ᵇn i n =
    begin
      configure-all (conf (suc i + n)) (translate' (suc n) y ys) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all (conf (suc i + n)) (translate' (suc n) y ys)
    ≡⟨ cong (λ eq → configure-all (conf eq) (translate' (suc n) y ys)) (+-suc i n) ⟨
      configure-all (conf (i + suc n)) (translate' (suc n) y ys)
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
      configure-all (conf (i + zero)) (translate' zero x xs)
    ≡⟨ cong (λ eq → configure-all (conf eq) (translate' zero x xs)) (+-identityʳ i) ⟩
      configure-all (conf i) (translate' zero x xs)
    ≡⟨⟩
      ⟦ translate (x ∷ xs) ⟧ (conf i)
    ∎

  translate'-preserves-fnoc : ∀ (x : Forest A) (xs : List (Forest A)) (n : ℕ) (c : Configuration) →
      configure-all c (translate' n x xs)
    ≡ VariantList.⟦ x ∷ xs ⟧ (fnoci n (List⁺.length (x ∷ xs)) (List⁺.length (x ∷ xs)) c)
  translate'-preserves-fnoc x [] n c = encode-idemp Forest A encoder c x
  translate'-preserves-fnoc x (y ∷ ys) n c with c (f , n) in eq
  ... | true rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq =
    begin
      configure-all c (encode-forest x) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all c (encode-forest x)
    ≡⟨ encode-idemp Forest A encoder c x ⟩
      x
    ∎
  ... | false rewrite n∸n≡0 (List⁺.length (y ∷ ys)) | +-identityʳ n | eq =
    begin
      configure-all c (translate' (suc n) y ys) ++ []
    ≡⟨ ++-identityʳ _ ⟩
      configure-all c (translate' (suc n) y ys)
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
      configure-all c (translate' zero x xs)
    ≡⟨ translate'-preserves-fnoc x xs zero c ⟩
      VariantList.⟦ x ∷ xs ⟧ (fnoc (List⁺.length (x ∷ xs)) c)
    ∎

VariantList→VT : LanguageCompiler VariantListL VTL
VariantList→VT = record
  { compile = translate
  ; config-compiler = λ e → record { to = conf ; from = fnoc (List⁺.length e) }
  ; preserves = λ {A} e →
    let open Preservation A in
      preserves-⊆ e , preserves-⊇ e
  }

VT≽VariantList : VTL ≽ VariantListL
VT≽VariantList = expressiveness-from-compiler VariantList→VT

VT-is-complete : Complete VTL
VT-is-complete = completeness-by-expressiveness VariantList-is-Complete VT≽VariantList
