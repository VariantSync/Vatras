open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.SyntacticExpressiveness.2CC≤ADT (F : 𝔽) where

open import Data.Nat using (suc; _≤_; s≤s; _+_)
import Data.Nat.Properties as ℕ
import Data.List as List
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (≅-sym; ≅[]→≅)
open import Vatras.Framework.Variants using (Rose)
import Vatras.Util.List as List
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.Translation.Lang.2CC.Rename using (2CC-rename)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Translation.LanguageMap using (ADT→2CC)
open import Vatras.SyntacticExpressiveness using (_≤Size_)
open import Vatras.SyntacticExpressiveness.Sizes F using (sizeRose; Sized2CC; size2CC; SizedADT; sizeADT)
open import Vatras.Lang.2CC.Encode using (encode; encoder)

ADT→2CC' : LanguageCompiler ADT.ADTL 2CC.2CCL
ADT→2CC' = ADT→2CC encoder

lemma2 : ∀ {i : Size} {A : 𝔸} (v : Rose i A) → size2CC (encode v) ≤ sizeRose v
lemma2 (a Rose.-< cs >-) =
  begin
    size2CC (encode (a Rose.-< cs >-))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< List.map encode cs >-)
  ≡⟨⟩
    suc (List.sum (List.map size2CC (List.map encode cs)))
  ≡⟨ Eq.cong (λ x → suc (List.sum x)) (List.map-∘ cs) ⟨
    suc (List.sum (List.map (size2CC ∘ encode) cs))
  ≤⟨ s≤s (List.sum-map-≤ (size2CC ∘ encode) sizeRose cs lemma2) ⟩
    suc (List.sum (List.map sizeRose cs))
  ≡⟨⟩
    sizeRose (a Rose.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning

lemma : ∀ {A : 𝔸} → (adt : ADT.ADT A) → size2CC (LanguageCompiler.compile ADT→2CC' adt) ≤ sizeADT adt
lemma (ADT.ADT.leaf v) = ℕ.m≤n⇒m≤1+n (lemma2 v)
lemma (D ADT.ADT.⟨ l , r ⟩) =
  begin
    size2CC (LanguageCompiler.compile ADT→2CC' (D ADT.ADT.⟨ l , r ⟩))
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ LanguageCompiler.compile ADT→2CC' l , LanguageCompiler.compile ADT→2CC' r ⟩)
  ≡⟨⟩
    suc (size2CC (LanguageCompiler.compile ADT→2CC' l) + size2CC (LanguageCompiler.compile ADT→2CC' r))
  ≤⟨ s≤s (ℕ.+-monoˡ-≤ (size2CC (LanguageCompiler.compile ADT→2CC' r)) (lemma l)) ⟩
    suc (sizeADT l + size2CC (LanguageCompiler.compile ADT→2CC' r))
  ≤⟨ s≤s (ℕ.+-monoʳ-≤ (sizeADT l) (lemma r)) ⟩
    suc (sizeADT l + sizeADT r)
  ∎
  where
  open ℕ.≤-Reasoning

2CC≤ADT : Sized2CC ≤Size SizedADT
2CC≤ADT = 1 , λ A adt → LanguageCompiler.compile ADT→2CC' adt , ≅-sym (≅[]→≅ (LanguageCompiler.preserves ADT→2CC' adt)) , Eq.subst (size2CC (LanguageCompiler.compile ADT→2CC' adt )≤_) (Eq.sym (ℕ.+-identityʳ (sizeADT adt))) (lemma adt)
