open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
module Vatras.SyntacticExpressiveness.2CC≤ADT (F : 𝔽) (A : 𝔸) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; z≤n; s≤s; _<_; _≮_; _<?_; _+_; pred; _*_; _^_; _≟_)
import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
import Data.List.Membership.Propositional as List
import Data.List.Membership.Propositional.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.NonEmpty.Properties as List⁺
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (_≅_; ≅-trans; ≅-sym; ≅[]→≅; _⊆_; ⊆-trans; _∈_)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.VariantGenerator (Rose ∞) A using (VariantGenerator)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
open import Vatras.Util.List using (find-or-last)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open import Vatras.Translation.Lang.2CC.Rename using (2CC-rename)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Translation.LanguageMap using (ADT→2CC)
open import Vatras.SyntacticExpressiveness A using (_≤Size_)
open import Vatras.SyntacticExpressiveness.Sizes F A using (sizeRose; Sized2CC; size2CC; SizedADT; sizeADT)
open import Vatras.Lang.2CC.Encode using (encode; encoder)
open import Vatras.Framework.Compiler using (_⊕_)

ADT→2CC' : LanguageCompiler ADT.ADTL 2CC.2CCL
ADT→2CC' = ADT→2CC encoder

lemma3 : ∀ {ℓ} {A : Set ℓ} (f g : A → ℕ) (xs : List A) → (∀ x → f x ≤ g x) → List.sum (List.map f xs) ≤ List.sum (List.map g xs)
lemma3 f g [] f≤g = z≤n
lemma3 f g (x ∷ xs) f≤g =
  begin
    List.sum (List.map f (x ∷ xs))
  ≡⟨⟩
    f x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoˡ-≤ (List.sum (List.map f xs)) (f≤g x) ⟩
    g x + List.sum (List.map f xs)
  ≤⟨ ℕ.+-monoʳ-≤ (g x) (lemma3 f g xs f≤g) ⟩
    g x + List.sum (List.map g xs)
  ≡⟨⟩
    List.sum (List.map g (x ∷ xs))
  ∎
  where
  open ℕ.≤-Reasoning

lemma2 : ∀ {i} (v : Rose i A) → size2CC (encode v) ≤ sizeRose v
lemma2 (a Rose.-< cs >-) =
  begin
    size2CC (encode (a Rose.-< cs >-))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< List.map encode cs >-)
  ≡⟨⟩
    suc (List.sum (List.map size2CC (List.map encode cs)))
  ≡⟨ Eq.cong (λ x → suc (List.sum x)) (List.map-∘ cs) ⟨
    suc (List.sum (List.map (size2CC ∘ encode) cs))
  ≤⟨ s≤s (lemma3 (size2CC ∘ encode) sizeRose cs lemma2) ⟩
    suc (List.sum (List.map sizeRose cs))
  ≡⟨⟩
    sizeRose (a Rose.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning

lemma : ∀ (adt : ADT.ADT A) → size2CC (LanguageCompiler.compile ADT→2CC' adt) ≤ sizeADT adt
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
2CC≤ADT = 1 , λ adt → LanguageCompiler.compile ADT→2CC' adt , ≅-sym (≅[]→≅ (LanguageCompiler.preserves ADT→2CC' adt)) , Eq.subst (size2CC (LanguageCompiler.compile ADT→2CC' adt )≤_) (Eq.sym (ℕ.+-identityʳ (sizeADT adt))) (lemma adt)
