open import Data.Nat using (ℕ; suc; _+_; _≤_; s≤s)
open import Relation.Binary using (DecidableEquality)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)

module Vatras.Succinctness.Relations.VariantList≤ADT
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  (sizeV : ∀ {A : 𝔸} → V A → ℕ)
  where

open import Data.Bool using (true; false; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.List as List using ([]; _∷_)
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (_⁺++⁺_)
open import Data.Product using (_,_; proj₁; proj₂)
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes; no)

open import Vatras.Util.AuxProofs using (Predicate-if)
import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (≅-sym; ≅[]→≅)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Succinctness.ProofDefinition V using (_≤ₛ_)
open import Vatras.Succinctness.Sizes using (SizedVariantList; sizeVariantList; SizedADT; sizeADT)

open import Vatras.Lang.All.Fixed F V
open ADT using (ADT; leaf; _⟨_,_⟩)
open VariantList using (VariantList)

open import Vatras.Lang.ADT.Path F V _==_ using (Path; _↣_; getValue; _∈?_)
open import Vatras.Translation.Lang.ADT.DeadElim F V _==_ using (kill-dead-below; kill-dead)
open import Vatras.Translation.Lang.ADT-to-VariantList F V _==_ using (ADT→VariantList; tr; tr-undead)

size-kill-dead : ∀ {A : 𝔸} (defined : Path) (adt : ADT A) → sizeADT sizeV (kill-dead-below defined adt) ≤ sizeADT sizeV adt
size-kill-dead defined (leaf v) = ℕ.≤-refl
size-kill-dead defined (D ⟨ l , r ⟩) with D ∈? defined
size-kill-dead defined (D ⟨ l , r ⟩) | yes D∈defined =
  begin
    sizeADT sizeV (if getValue D∈defined then kill-dead-below defined l else kill-dead-below defined r)
  ≡⟨ Bool.if-float (sizeADT sizeV) (getValue D∈defined) ⟩
    (if getValue D∈defined then sizeADT sizeV (kill-dead-below defined l) else sizeADT sizeV (kill-dead-below defined r))
  ≤⟨ Predicate-if (_≤ _) (getValue D∈defined)
      (ℕ.≤-trans (size-kill-dead defined l) (ℕ.m≤m+n (sizeADT sizeV l) (sizeADT sizeV r)))
      (ℕ.≤-trans (size-kill-dead defined r) (ℕ.m≤n+m (sizeADT sizeV r) (sizeADT sizeV l)))
  ⟩
    sizeADT sizeV l + sizeADT sizeV r
  <⟨ ℕ.n<1+n (sizeADT sizeV l + sizeADT sizeV r) ⟩
    suc (sizeADT sizeV l + sizeADT sizeV r)
  ≡⟨⟩
    sizeADT sizeV (D ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning
size-kill-dead defined (D ⟨ l , r ⟩) | no D∉defined =
  begin
    sizeADT sizeV (D ⟨ kill-dead-below (D ↣ true ∷ defined) l , kill-dead-below (D ↣ false ∷ defined) r ⟩)
  ≡⟨⟩
    suc (sizeADT sizeV (kill-dead-below (D ↣ true ∷ defined) l) + sizeADT sizeV (kill-dead-below (D ↣ false ∷ defined) r))
  ≤⟨ s≤s (ℕ.+-mono-≤ (size-kill-dead (D ↣ true ∷ defined) l) (size-kill-dead (D ↣ false ∷ defined) r)) ⟩
    suc (sizeADT sizeV l + sizeADT sizeV r)
  ≡⟨⟩
    sizeADT sizeV (D ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

size-tr : ∀ {A : 𝔸} (adt : ADT A) → sizeVariantList {V} sizeV (tr adt) ≤ sizeADT sizeV adt
size-tr (leaf v) =
  begin
    sizeVariantList {V} sizeV (tr (leaf v))
  ≡⟨⟩
    sizeV v + 0
  ≡⟨ ℕ.+-identityʳ (sizeV v) ⟩
    sizeV v
  <⟨ ℕ.n<1+n (sizeV v) ⟩
    1 + sizeV v
  ≡⟨⟩
    sizeADT sizeV (leaf v)
  ∎
  where
  open ℕ.≤-Reasoning
size-tr (f ⟨ l , r ⟩) =
  begin
    sizeVariantList {V} sizeV (tr (f ⟨ l , r ⟩))
  ≡⟨⟩
    sizeVariantList {V} sizeV (tr l ⁺++⁺ tr r)
  ≡⟨⟩
    List.sum (List⁺.toList (List⁺.map sizeV (tr l ⁺++⁺ tr r)))
  ≡⟨ Eq.cong (λ x → List.sum (List⁺.toList x)) (List.map-⁺++⁺ sizeV (tr l) (tr r)) ⟩
    List.sum (List⁺.toList (List⁺.map sizeV (tr l) ⁺++⁺ List⁺.map sizeV (tr r)))
  ≡⟨ List.sum-++ (List⁺.toList (List⁺.map sizeV (tr l))) (List⁺.toList (List⁺.map sizeV (tr r))) ⟩
    List.sum (List⁺.toList (List⁺.map sizeV (tr l))) + List.sum (List⁺.toList (List⁺.map sizeV (tr r)))
  ≡⟨⟩
    sizeVariantList {V} sizeV (tr l) + sizeVariantList {V} sizeV (tr r)
  ≤⟨ ℕ.+-mono-≤ (size-tr l) (size-tr r) ⟩
    sizeADT sizeV l + sizeADT sizeV r
  <⟨ ℕ.n<1+n (sizeADT sizeV l + sizeADT sizeV r) ⟩
    suc (sizeADT sizeV l + sizeADT sizeV r)
  ≡⟨⟩
    sizeADT sizeV (f ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

size-tr-kill-dead : ∀ {A : 𝔸} (adt : ADT A) → sizeVariantList {V} sizeV (tr-undead (kill-dead adt)) ≤ sizeADT sizeV adt
size-tr-kill-dead adt =
  begin
    sizeVariantList {V} sizeV (tr-undead (kill-dead adt))
  ≤⟨ size-tr (kill-dead-below [] adt) ⟩
    sizeADT sizeV (kill-dead-below [] adt)
  ≤⟨ size-kill-dead [] adt ⟩
    sizeADT sizeV adt
  ∎
  where
  open ℕ.≤-Reasoning

VariantList≤ADT : SizedVariantList V sizeV ≤ₛ SizedADT F V sizeV
VariantList≤ADT .proj₁ = 1
VariantList≤ADT .proj₂ A e₂ e₂-translatable = LanguageCompiler.compile ADT→VariantList e₂ , ≅-sym (≅[]→≅ (LanguageCompiler.preserves ADT→VariantList e₂)) , ℕ.≤-trans (size-tr-kill-dead e₂) (ℕ.≤-reflexive (Eq.sym (ℕ.+-identityʳ (sizeADT sizeV e₂))))
