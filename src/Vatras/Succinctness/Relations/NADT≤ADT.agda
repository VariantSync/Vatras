open import Data.Nat using (ℕ; suc; _+_; _≟_; s≤s)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)

module Vatras.Succinctness.Relations.NADT≤ADT (F : 𝔽) (V : 𝕍) (sizeV : ∀ {A : 𝔸} → V A → ℕ) (sizeV : ∀ {A : 𝔸} → V A → ℕ) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Data.List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (_∷_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (∞)

open import Vatras.Util.List as List using (find-or-last)
open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]→≅)
open import Vatras.Succinctness.ProofDefinition V using (_≤ₛ_)
open import Vatras.Succinctness.Sizes using (SizedNADT; sizeNADT; SizedADT; sizeADT)
open import Vatras.Lang.All.Fixed F V
open ADT using (ADT; _⟨_,_⟩; leaf)
open NADT using (NADT; _⟨_⟩; leaf)

open import Vatras.Translation.Lang.ADT-to-VariantList using ()

translate : ∀ {A : 𝔸} → ADT A → NADT ∞ A
translate (leaf v) = leaf v
translate (f ⟨ l , r ⟩) = f ⟨ translate l ∷ translate r ∷ [] ⟩

conf : NADT.Configuration → ADT.Configuration
conf config f with config f ≟ 0
conf config f | yes _ = true
conf config f | no _ = false

fnoc : ADT.Configuration → NADT.Configuration
fnoc config f = if config f then 0 else 1

translate-preserves-⊆ : ∀ {A : 𝔸} → (adt : ADT A) → NADT.⟦ translate adt ⟧ ⊆[ conf ] ADT.⟦ adt ⟧
translate-preserves-⊆ (leaf v) config = refl
translate-preserves-⊆ (f ⟨ l , r ⟩) config with config f ≟ 0
translate-preserves-⊆ (f ⟨ l , r ⟩) config | yes config-f≡0 =
    NADT.⟦ find-or-last (config f) (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last x (translate l ∷ translate r ∷ []) ⟧ config) config-f≡0 ⟩
    NADT.⟦ find-or-last 0 (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨⟩
    NADT.⟦ translate l ⟧ config
  ≡⟨ translate-preserves-⊆ l config ⟩
    ADT.⟦ l ⟧ (conf config)
  ≡⟨⟩
    (if true then ADT.⟦ l ⟧ (conf config) else ADT.⟦ r ⟧ (conf config))
  ∎
  where
  open Eq.≡-Reasoning
translate-preserves-⊆ (f ⟨ l , r ⟩) config | no config-f≢0 =
    NADT.⟦ find-or-last (config f) (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨ Eq.cong (λ x → NADT.⟦ x ⟧ config) (List.find-or-last-last (config f) (translate l ∷ translate r ∷ []) (s≤s (ℕ.n≢0⇒n>0 config-f≢0))) ⟩
    NADT.⟦ List⁺.last (translate l ∷ translate r ∷ []) ⟧ config
  ≡⟨⟩
    NADT.⟦ translate r ⟧ config
  ≡⟨ translate-preserves-⊆ r config ⟩
    ADT.⟦ r ⟧ (conf config)
  ≡⟨⟩
    (if false then ADT.⟦ l ⟧ (conf config) else ADT.⟦ r ⟧ (conf config))
  ∎
  where
  open Eq.≡-Reasoning

translate-preserves-⊇ : ∀ {A : 𝔸} → (adt : ADT A) → ADT.⟦ adt ⟧ ⊆[ fnoc ] NADT.⟦ translate adt ⟧
translate-preserves-⊇ (leaf v) config = refl
translate-preserves-⊇ (f ⟨ l , r ⟩) config with config f
translate-preserves-⊇ (f ⟨ l , r ⟩) config | true = translate-preserves-⊇ l config
translate-preserves-⊇ (f ⟨ l , r ⟩) config | false = translate-preserves-⊇ r config

translate-preserves : ∀ {A : 𝔸} → (adt : ADT A) → NADT.⟦ translate adt ⟧ ≅[ conf ][ fnoc ] ADT.⟦ adt ⟧
translate-preserves adt = translate-preserves-⊆ adt and translate-preserves-⊇ adt

lemma : ∀ {A : 𝔸} → (adt : ADT A) → sizeNADT sizeV (translate adt) ≡ sizeADT sizeV adt
lemma (leaf v) = refl
lemma (f ⟨ l , r ⟩) =
    sizeNADT sizeV (translate (f ⟨ l , r ⟩))
  ≡⟨⟩
    suc (sizeNADT sizeV (translate l) + (sizeNADT sizeV (translate r) + 0))
  ≡⟨ Eq.cong (λ x → suc (sizeNADT sizeV (translate l) + x)) (ℕ.+-identityʳ (sizeNADT sizeV (translate r))) ⟩
    suc (sizeNADT sizeV (translate l) + sizeNADT sizeV (translate r))
  ≡⟨ Eq.cong₂ (λ x y → suc (x + y)) (lemma l) (lemma r) ⟩
    suc (sizeADT sizeV l + sizeADT sizeV r)
  ≡⟨⟩
    sizeADT sizeV (f ⟨ l , r ⟩)
  ∎
  where
  open Eq.≡-Reasoning

NADT≤ADT : SizedNADT F V sizeV ≤ₛ SizedADT F V sizeV
NADT≤ADT .proj₁ = 1
NADT≤ADT .proj₂ A e₂ e₂-translatable = translate e₂ and ≅[]→≅ (translate-preserves e₂) and ℕ.≤-reflexive (Eq.trans (lemma e₂) (Eq.sym (ℕ.+-identityʳ (sizeADT sizeV e₂))))
