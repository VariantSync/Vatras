open import Vatras.Framework.Definitions using (𝔸; 𝕍)
module Vatras.Succinctness.DefinitionEquivalence (V : 𝕍) where

open import Data.Empty using (⊥-elim)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax; ∄-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _≤?_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)

open import Vatras.Data.EqIndexedSet using (≅-refl; ≅-sym; ≅-trans)
open import Vatras.Framework.VariabilityLanguage using (Expression)
open import Vatras.Framework.Relation.Expression V using (_,_⊢_≣_)
open import Vatras.Succinctness.Sizes using (SizedLang; Lang; size)
open import Vatras.Succinctness.DesignedDefinition V using (minimalExpression; design)
open import Vatras.Succinctness.ProofDefinition V using (_≤ₛ[_]_)

simplification→design
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : SizedLang V)
  → VL₁ ≤ₛ[ f ] VL₂
  → design f VL₁ VL₂
simplification→design f VL₁ VL₂ (m , simplification) .proj₁ = m
simplification→design f VL₁ VL₂ (m , simplification) .proj₂ A e₁ e₂ e₁≅e₂ e₁-minimal e₂-minimal
  with simplification A e₂ (e₁ , ≅-sym e₁≅e₂)
... | e₁' , e₁'≅e₂ , e₁'≤e₂
    = ℕ.≤-trans (e₁-minimal e₁' (≅-trans e₁≅e₂ (≅-sym e₁'≅e₂))) e₁'≤e₂

open import Axiom.ExcludedMiddle
module Classical (excludedMiddle : ∀ {ℓ} → ExcludedMiddle ℓ) where

  ∃minimalExpression
    : {A : 𝔸}
    → (VL : SizedLang V)
    → (e : Expression (Lang VL) A)
    → Σ[ e' ∈ Expression (Lang VL) A ] (Lang VL , Lang VL ⊢ e ≣ e') × minimalExpression VL e'
  ∃minimalExpression {A} VL e = go (size VL e) zero (Eq.sym (ℕ.*-identityˡ (size VL e))) λ where ()
    where
    open ℕ.≤-Reasoning

    go
      : (m n : ℕ)
      → size VL e ≡ m + n
      → (∄[ e' ] (Lang VL , Lang VL ⊢ e ≣ e') × size VL e' < n)
      → Σ[ e' ∈ Expression (Lang VL) A ] (Lang VL , Lang VL ⊢ e ≣ e') × minimalExpression VL e'
    go zero n size≡m+n ∄smaller = e , ≅-refl , isMinimal
      where
      isMinimal : (e' : Expression (Lang VL) A) → Lang VL , Lang VL ⊢ e ≣ e' → size VL e ≤ size VL e'
      isMinimal e' e≅e' with size VL e ≤? size VL e'
      isMinimal e' e≅e' | yes e≤e' = e≤e'
      isMinimal e' e≅e' | no e≰e' = ⊥-elim (∄smaller (e' , e≅e' , (
        begin-strict
          size VL e'
        <⟨ ℕ.≰⇒> e≰e' ⟩
          size VL e
        ≡⟨ size≡m+n ⟩
          n
        ∎)))
    go (suc m) n size≡m+n ∄smaller with excludedMiddle {P = ∃[ e' ] (Lang VL , Lang VL ⊢ e ≣ e') × size VL e' < suc n}
    go (suc m) n size≡m+n ∄smaller | no ∄e'<e = go m (suc n) (Eq.trans size≡m+n (Eq.sym (ℕ.+-suc m n))) ∄e'<e
    go (suc m) n size≡m+n ∄smaller | yes (e' , e≅e' , e'≤e) = e' , e≅e' , isMinimal
      where
      isMinimal : (e'' : Expression (Lang VL) A) → Lang VL , Lang VL ⊢ e' ≣ e'' → size VL e' ≤ size VL e''
      isMinimal e'' e'≅e'' with size VL e' ≤? size VL e''
      isMinimal e'' e'≅e'' | yes e'≤e'' = e'≤e''
      isMinimal e'' e'≅e'' | no e'≰e'' = ⊥-elim (∄smaller (e'' , ≅-trans e≅e' e'≅e'' , (
        begin-strict
          size VL e''
        <⟨ ℕ.≰⇒> e'≰e'' ⟩
          size VL e'
        ≤⟨ ℕ.≤-pred e'≤e ⟩
          n
        ∎)))

  design→simplification
    : (f : ℕ → ℕ)
    → (∀ n m → n ≤ m → f n ≤ f m)
    → (VL₁ VL₂ : SizedLang V)
    → design f VL₁ VL₂
    → VL₁ ≤ₛ[ f ] VL₂
  design→simplification f f-monotone VL₁ VL₂ (m , design) .proj₁ = m
  design→simplification f f-monotone VL₁ VL₂ (m , design) .proj₂ A e₂ (e₁ , e₂≅e₁)
    with ∃minimalExpression VL₁ e₁ | ∃minimalExpression VL₂ e₂
  ... | e₁' , e₁≅e₁' , e₁'-minimal | e₂' , e₂≅e₂' , e₂'-minimal
    = e₁' , ≅-sym (≅-trans e₂≅e₁ e₁≅e₁') , (
      begin
        size VL₁ e₁'
      ≤⟨ design A e₁' e₂' (≅-trans (≅-sym (≅-trans e₂≅e₁ e₁≅e₁')) e₂≅e₂') e₁'-minimal e₂'-minimal ⟩
        m * f (size VL₂ e₂')
      ≤⟨ ℕ.*-monoʳ-≤ m (f-monotone (size VL₂ e₂') (size VL₂ e₂) (e₂'-minimal e₂ (≅-sym e₂≅e₂'))) ⟩
        m * f (size VL₂ e₂)
      ∎)
    where
    open ℕ.≤-Reasoning
