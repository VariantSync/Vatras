open import Vatras.Framework.Definitions
open import Vatras.Framework.VariabilityLanguage
open import Data.Nat hiding (_≡ᵇ_)
module Vatras.Succinctness.DesignedDefinition (V : 𝕍) (size : {A : 𝔸} (VL : VariabilityLanguage V) → Expression VL A → ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax; ∄-syntax; map₁)
open import Data.Sum using (_⊎_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)
open import Function using (id)

open import Vatras.Data.EqIndexedSet using (≅-refl; ≅-sym; ≅-trans)
open import Vatras.Framework.Relation.Expression V
open import Vatras.Framework.Relation.Expressiveness V

size≤
  : {A : 𝔸}
  → (m : ℕ)
  → (f : ℕ → ℕ)
  → (VL₁ VL₂ : VariabilityLanguage V)
  → Expression VL₁ A
  → Expression VL₂ A
  → Set
size≤ m f VL₁ VL₂ e₁ e₂ =
  size VL₁ e₁ ≤ m * f (size VL₂ e₂)

minimalExpression
  : {A : 𝔸} (VL : VariabilityLanguage V)
  → Expression VL A
  → Set _
minimalExpression {A} VL e =
  ∀ (e' : Expression VL A) (e≅e' : VL , VL ⊢ e ≣ e')
  → size≤ 1 id VL VL e e'

design
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : VariabilityLanguage V)
  → Set _
design f VL₁ VL₂ =
  ∀ (A : 𝔸)
  → Σ[ m ∈ ℕ ]
  ∀ (e₁ : Expression VL₁ A)
    (e₂ : Expression VL₂ A)
  → VL₁ , VL₂ ⊢ e₁ ≣ e₂
  → minimalExpression VL₁ e₁
  → minimalExpression VL₂ e₂
  → size≤ m f VL₁ VL₂ e₁ e₂

relation
  : (VL₁ VL₂ : VariabilityLanguage V)
  → Set _
relation VL₁ VL₂ = design id VL₁ VL₂

translatable
  : (VL₁ VL₂ : VariabilityLanguage V)
  → {A : 𝔸}
  → (e₁ : Expression VL₁ A)
  → Set _
translatable VL₁ VL₂ {A} e₁ =
  Σ[ e₂ ∈ Expression VL₂ A ] VL₂ , VL₁ ⊢ e₂ ≣ e₁

simplification
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : VariabilityLanguage V)
  → Set _
simplification f VL₁ VL₂ =
  ∀ (A : 𝔸) →
  Σ[ m ∈ ℕ ]
  ∀ (e₂ : Expression VL₂ A)
  → translatable VL₂ VL₁ e₂
  → Σ[ e₁ ∈ Expression VL₁ A ]
      (VL₁ , VL₂ ⊢ e₁ ≣ e₂)
    × size≤ m f VL₁ VL₂ e₁ e₂

simplification→design
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : VariabilityLanguage V)
  → simplification f VL₁ VL₂
  → design f VL₁ VL₂

simplification→design f VL₁ VL₂ simplification A with simplification A
simplification→design f VL₁ VL₂ simplification A | m , simplification' = m , go
  where
  open ℕ.≤-Reasoning

  go :
    ∀ (e₁ : Expression VL₁ A) (e₂ : Expression VL₂ A) (e₁≅e₂ : VL₁ , VL₂ ⊢ e₁ ≣ e₂)
    → minimalExpression VL₁ e₁
    → minimalExpression VL₂ e₂
    → size≤ m f VL₁ VL₂ e₁ e₂
  go e₁ e₂ e₁≅e₂ e₁-minimal e₂-minimal with simplification' e₂ (e₁ , e₁≅e₂)
  go e₁ e₂ e₁≅e₂ e₁-minimal e₂-minimal | e₁' , e₁'≅e₂ , e₁'≤e₂ = ℕ.≤-trans (e₁-minimal e₁' (≅-trans e₁≅e₂ (≅-sym e₁'≅e₂))) (
    begin
      1 * size VL₁ e₁'
    ≡⟨ ℕ.*-identityˡ (size VL₁ e₁') ⟩
      size VL₁ e₁'
    ≤⟨ e₁'≤e₂ ⟩
      m * f (size VL₂ e₂)
    ∎)

open import Axiom.ExcludedMiddle
module Classical (excludedMiddle : ∀ {ℓ} → ExcludedMiddle ℓ) where

  ∃minimalExpression
    : {A : 𝔸}
    → (VL : VariabilityLanguage V)
    → (e : Expression VL A)
    → Σ[ e' ∈ Expression VL A ] (VL , VL ⊢ e ≣ e') × minimalExpression VL e'
  ∃minimalExpression {A} VL e = go (size VL e) zero (Eq.sym (ℕ.*-identityˡ (size VL e))) λ where ()
    where
    open ℕ.≤-Reasoning

    go
      : (m n : ℕ)
      → size VL e ≡ m + n
      → (∄[ e' ] (VL , VL ⊢ e ≣ e') × size {A} VL e' < n)
      → Σ[ e' ∈ Expression VL A ] (VL , VL ⊢ e ≣ e') × minimalExpression VL e'
    go zero n size≡m+n ∄smaller = e , ≅-refl , isMinimal
      where
      isMinimal : (e' : Expression VL A) → VL , VL ⊢ e ≣ e' → size≤ 1 id VL VL e e'
      isMinimal e' e≅e' with size VL e ≤? size VL e'
      isMinimal e' e≅e' | yes e≤e' =
        begin
          size VL e
        ≤⟨ e≤e' ⟩
          size VL e'
        ≡⟨ ℕ.*-identityˡ (size VL e') ⟨
          1 * size VL e'
        ∎
      isMinimal e' e≅e' | no e≰e' = ⊥-elim (∄smaller (e' , e≅e' , (
        begin-strict
          size VL e'
        <⟨ ℕ.≰⇒> e≰e' ⟩
          size VL e
        ≡⟨ size≡m+n ⟩
          n
        ∎)))
    go (suc m) n size≡m+n ∄smaller with excludedMiddle {P = ∃[ e' ] (VL , VL ⊢ e ≣ e') × size {A} VL e' < suc n}
    go (suc m) n size≡m+n ∄smaller | no ∄e'<e = go m (suc n) (Eq.trans size≡m+n (Eq.sym (ℕ.+-suc m n))) ∄e'<e
    go (suc m) n size≡m+n ∄smaller | yes (e' , e≅e' , e'≤e) = e' , e≅e' , isMinimal
      where
      isMinimal : (e'' : Expression VL A) → VL , VL ⊢ e' ≣ e'' → size≤ 1 id VL VL e' e''
      isMinimal e'' e'≅e'' with size VL e' ≤? size VL e''
      isMinimal e'' e'≅e'' | yes e'≤e'' =
        begin
          size VL e'
        ≤⟨ e'≤e'' ⟩
          size VL e''
        ≡⟨ ℕ.*-identityˡ (size VL e'') ⟨
          1 * size VL e''
        ∎
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
    → (VL₁ VL₂ : VariabilityLanguage V)
    → design f VL₁ VL₂
    → simplification f VL₁ VL₂
  design→simplification f f-monotone VL₁ VL₂ design A with design A
  design→simplification f f-monotone VL₁ VL₂ design A | m , design' = m , go
    where
    open ℕ.≤-Reasoning

    go :
      ∀ (e₂ : Expression VL₂ A)
      → Σ[ e₁ ∈ Expression VL₁ A ]
        (VL₁ , VL₂ ⊢ e₁ ≣ e₂)
      → Σ[ e₁ ∈ Expression VL₁ A ]
          (VL₁ , VL₂ ⊢ e₁ ≣ e₂)
        × size≤ m f VL₁ VL₂ e₁ e₂
    go e₂ (e₁ , e₁≅e₂) with ∃minimalExpression VL₁ e₁ | ∃minimalExpression VL₂ e₂
    go e₂ (e₁ , e₁≅e₂) | e₁' , e₁≅e₁' , e₁'-minimal | e₂' , e₂≅e₂' , e₂'-minimal = e₁' , ≅-trans (≅-sym e₁≅e₁') e₁≅e₂ , (
      begin
        size VL₁ e₁'
      ≤⟨ design' e₁' e₂' (≅-trans (≅-sym e₁≅e₁') (≅-trans e₁≅e₂ e₂≅e₂')) e₁'-minimal e₂'-minimal ⟩
        m * f (size VL₂ e₂')
      ≤⟨ ℕ.*-monoʳ-≤ m (f-monotone (size VL₂ e₂') (1 * size VL₂ e₂) (e₂'-minimal e₂ (≅-sym e₂≅e₂'))) ⟩
        m * f (1 * size VL₂ e₂)
      ≡⟨ Eq.cong (λ x → m * f x) (ℕ.*-identityˡ (size VL₂ e₂)) ⟩
        m * f (size VL₂ e₂)
      ∎)
