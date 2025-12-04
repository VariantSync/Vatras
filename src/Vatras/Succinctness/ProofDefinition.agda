open import Vatras.Framework.Definitions using (𝔸; 𝕍)
module Vatras.Succinctness.ProofDefinition (V : 𝕍) where

import Axiom.ExcludedMiddle
import Axiom.DoubleNegationElimination
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; _≤_; _>_; _*_)
import Data.Nat.Properties as ℕ
open import Data.Product as Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Function using (id; _∘_)
open import Relation.Binary using (_Preserves_⟶_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; ¬∃⟶∀¬)
open import Relation.Unary using (_∈_)

open import Vatras.Data.EqIndexedSet using (≅-refl; ≅-sym; ≅-trans; ≅→≅[]; ⊆-index)
open import Vatras.Util.Big-O using (𝒪[_])
open Vatras.Util.Big-O.Examples using (n∈𝒪[n])
open import Vatras.Framework.Relation.Expression V using (_,_⊢_≣_)
open import Vatras.Framework.Relation.Expressiveness V using (_≽_; _≋_; ≽-trans; ≋-refl; ≋-sym; ≋-trans)
open import Vatras.Framework.VariabilityLanguage using (Expression)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Succinctness.Sizes using (SizedLang; Lang; size)

translatable
  : (L₁ L₂ : SizedLang V)
  → {A : 𝔸}
  → (e₁ : Expression (Lang L₁) A)
  → Set _
translatable L₁ L₂ {A} e₁ =
  Σ[ e₂ ∈ Expression (Lang L₂) A ]
  Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂

_≤ₛ[_]_
  : (L₁ : SizedLang V)
  → (f : ℕ → ℕ)
  → (L₂ : SizedLang V)
  → Set _
L₁ ≤ₛ[ f ] L₂ =
  Σ[ n ∈ ℕ ]
  ∀ (A : 𝔸) →
  ∀ (e₂ : Expression (Lang L₂) A)
  → translatable L₂ L₁ e₂
  → Σ[ e₁ ∈ Expression (Lang L₁) A ]
      Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
    × size L₁ e₁ ≤ n * f (size L₂ e₂)

_≰ₛ[_]_
  : (L₁ : SizedLang V)
  → (f : ℕ → ℕ)
  → (L₂ : SizedLang V)
  → Set _
L₁ ≰ₛ[ f ] L₂ =
  ∀ (n : ℕ) →
  Σ[ A ∈ 𝔸 ]
  Σ[ e₂ ∈ Expression (Lang L₂) A ]
    translatable L₂ L₁ e₂
  × ∀ (e₁ : Expression (Lang L₁) A)
    → Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
    → size L₁ e₁ > n * f (size L₂ e₂)


≤ₛ[]-growthFactor : {L₁ L₂ : SizedLang V} (f : ℕ → ℕ) → L₁ ≤ₛ[ f ] L₂ → ℕ
≤ₛ[]-growthFactor f = proj₁

at-least-linear : (ℕ → ℕ) → Set
at-least-linear f = id ∈ 𝒪[ f ]

monotonic : (ℕ → ℕ) → Set
monotonic f = f Preserves _≤_ ⟶ _≤_


≤ₛ[]-refl : {L : SizedLang V} {f : ℕ → ℕ} → at-least-linear f → L ≤ₛ[ f ] L
≤ₛ[]-refl {L} (n , id≤f) = n , λ A e e-translatable → e , ≅-refl , id≤f (size L e)

≤ₛ[]-transitive
  : {L₁ L₂ L₃ : SizedLang V}
  → (f g : ℕ → ℕ)
  → monotonic f
  → Lang L₁ ≽ Lang L₂
  → Lang L₂ ≽ Lang L₃
  → L₁ ≤ₛ[ f ] L₂
  → (L₂≤ₛL₃ : L₂ ≤ₛ[ g ] L₃)
  → L₁ ≤ₛ[ (λ n → f (≤ₛ[]-growthFactor g L₂≤ₛL₃ * g n)) ] L₃
≤ₛ[]-transitive {L₁} {L₂} {L₃} f g f-monotone L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₁ = n₁
≤ₛ[]-transitive {L₁} {L₂} {L₃} f g f-monotone L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable with L₃→L₂ A e₃ (L₂≽L₃ e₃)
≤ₛ[]-transitive {L₁} {L₂} {L₃} f g f-monotone L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable | e₂ , e₂≅e₃ , e₁≤e₂ with L₂→L₁ A e₂ (L₁≽L₂ e₂)
≤ₛ[]-transitive {L₁} {L₂} {L₃} f g f-monotone L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable | e₂ , e₂≅e₃ , e₂≤e₃ | e₁ , e₁≅e₂ , e₁≤e₂
  = e₁ , ≅-trans e₁≅e₂ e₂≅e₃ ,
    (begin
      size L₁ e₁
    ≤⟨ e₁≤e₂ ⟩
      n₁ * f (size L₂ e₂)
    ≤⟨ ℕ.*-monoʳ-≤ n₁ (f-monotone e₂≤e₃) ⟩
      n₁ * f (n₂ * g (size L₃ e₃))
    ∎)
  where
  open ℕ.≤-Reasoning


_≤ₛ_ : SizedLang V → SizedLang V → Set₁
L₁ ≤ₛ L₂ = L₁ ≤ₛ[ id ] L₂

_=ₛ_ : SizedLang V → SizedLang V → Set₁
L₁ =ₛ L₂ = L₁ ≤ₛ L₂ × L₂ ≤ₛ L₁

_≰ₛ_ : SizedLang V → SizedLang V → Set₁
L₁ ≰ₛ L₂ = L₁ ≰ₛ[ id ] L₂

_<ₛ_ : SizedLang V → SizedLang V → Set₁
L₁ <ₛ L₂ = L₁ ≤ₛ L₂ × L₂ ≰ₛ L₁


≤ₛ-refl : {L : SizedLang V} → L ≤ₛ L
≤ₛ-refl = ≤ₛ[]-refl n∈𝒪[n]

≤ₛ-reflexive : {L₁ L₂ : SizedLang V} → L₁ =ₛ L₂ → L₁ ≤ₛ L₂
≤ₛ-reflexive (L₁≤ₛL₂ , L₂≤ₛL₁) = L₁≤ₛL₂

≤ₛ-transitive : {L₁ L₂ L₃ : SizedLang V} →
    Lang L₁ ≽ Lang L₂
  → Lang L₂ ≽ Lang L₃
  → L₁ ≤ₛ L₂
  → L₂ ≤ₛ L₃
  → L₁ ≤ₛ L₃
≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₁ = n₁ * n₂
≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable with L₃→L₂ A e₃ (L₂≽L₃ e₃)
≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable | e₂ , e₂≅e₃ , e₁≤e₂ with L₂→L₁ A e₂ (L₁≽L₂ e₂)
≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ e₃-translatable | e₂ , e₂≅e₃ , e₂≤e₃ | e₁ , e₁≅e₂ , e₁≤e₂
  = e₁ , ≅-trans e₁≅e₂ e₂≅e₃ ,
    (begin
      size L₁ e₁
    ≤⟨ e₁≤e₂ ⟩
      n₁ * size L₂ e₂
    ≤⟨ ℕ.*-monoʳ-≤ n₁ e₂≤e₃ ⟩
      n₁ * (n₂ * size L₃ e₃)
    ≡⟨ ℕ.*-assoc n₁ n₂ (size L₃ e₃) ⟨
      n₁ * n₂ * size L₃ e₃
    ∎)
  where
  open ℕ.≤-Reasoning

≤ₛ-antisymmetric : {L₁ L₂ : SizedLang V} → L₁ ≤ₛ L₂ → L₂ ≤ₛ L₁ → L₁ =ₛ L₂
≤ₛ-antisymmetric L₁≤ₛL₂ L₂≤ₛL₁ = L₁≤ₛL₂ , L₂≤ₛL₁


=ₛ-reflexive : {L : SizedLang V} → L =ₛ L
=ₛ-reflexive = ≤ₛ-refl , ≤ₛ-refl

=ₛ-symmetric : {L₁ L₂ : SizedLang V} → L₁ =ₛ L₂ → L₂ =ₛ L₁
=ₛ-symmetric (L₁≤ₛL₂ , L₂≤ₛL₁) = L₂≤ₛL₁ , L₁≤ₛL₂

=ₛ-transitive : {L₁ L₂ L₃ : SizedLang V} → Lang L₁ ≋ Lang L₂ → Lang L₂ ≋ Lang L₃ → L₁ =ₛ L₂ → L₂ =ₛ L₃ → L₁ =ₛ L₃
=ₛ-transitive (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂) (L₁≤ₛL₂ , L₂≤ₛL₁) (L₂≤ₛL₃ , L₃≤ₛL₂) = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃ , ≤ₛ-transitive L₃≽L₂ L₂≽L₁ L₃≤ₛL₂ L₂≤ₛL₁

<ₛ→≤ₛ : {L₁ L₂ : SizedLang V} → L₁ <ₛ L₂ → L₁ ≤ₛ L₂
<ₛ→≤ₛ (L₁≤ₛL₂ , L₂≰ₛL₁) = L₁≤ₛL₂

≤ₛ-≱ₛ-transitive :
  ∀ {L₁ L₂ L₃ : SizedLang V}
  → Lang L₁ ≽ Lang L₂
  → L₁ ≤ₛ L₂
  → L₃ ≰ₛ L₂
  → L₃ ≰ₛ L₁
≤ₛ-≱ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₁≤ₛL₂@(m , L₂→L₁) L₃≰ₛL₂ n with L₃≰ₛL₂ (n * m)
≤ₛ-≱ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₁≤ₛL₂@(m , L₂→L₁) L₃≰ₛL₂ n | A , e₂ , (e₃ , e₂≅e₃) , e₂< with L₂→L₁ A e₂ (L₁≽L₂ e₂)
≤ₛ-≱ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₁≤ₛL₂@(m , L₂→L₁) L₃≰ₛL₂ n | A , e₂ , (e₃ , e₂≅e₃) , e₂< | e₁ , e₁≅e₂ , e₁≤e₂
  = A , e₁ , (e₃ , ≅-trans e₁≅e₂ e₂≅e₃) , λ e₃' e₃≅e₁ →
    begin-strict
      n * size L₁ e₁
    ≤⟨ ℕ.*-monoʳ-≤ n e₁≤e₂ ⟩
      n * (m * size L₂ e₂)
    ≡⟨ ℕ.*-assoc n m (size L₂ e₂) ⟨
      n * m * size L₂ e₂
    <⟨ e₂< e₃' (≅-trans e₃≅e₁ e₁≅e₂) ⟩
      size L₃ e₃'
    ∎
  where
  open ℕ.≤-Reasoning

≤ₛ-<ₛ-transitive : {L₁ L₂ L₃ : SizedLang V} → Lang L₁ ≽ Lang L₂ → Lang L₂ ≽ Lang L₃ → L₁ ≤ₛ L₂ → L₂ <ₛ L₃ → L₁ <ₛ L₃
≤ₛ-<ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₁ = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
≤ₛ-<ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₂ = ≤ₛ-≱ₛ-transitive L₁≽L₂ L₁≤ₛL₂ L₃≰ₛL₂

≱ₛ-≤ₛ-transitive :
  ∀ {L₁ L₂ L₃ : SizedLang V}
  → Lang L₂ ≋ Lang L₃
  → L₂ ≰ₛ L₁
  → L₂ ≤ₛ L₃
  → L₃ ≰ₛ L₁
≱ₛ-≤ₛ-transitive {L₁} {L₂} {L₃} (L₂≽L₃ , L₃≽L₂) L₂≰ₛL₁ L₂≤ₛL₃@(m , L₃→L₂) n with L₂≰ₛL₁ (m * n)
≱ₛ-≤ₛ-transitive {L₁} {L₂} {L₃} (L₂≽L₃ , L₃≽L₂) L₂≰ₛL₁ L₂≤ₛL₃@(m , L₃→L₂) n | A , e₁ , (e₂ , e₁≅e₂) , e₁<
  = A , e₁ , Product.map₂ (≅-trans e₁≅e₂) (L₃≽L₂ e₂) , go
  where
  go : (e₃ : Expression (Lang L₃) A) → Lang L₃ , Lang L₁ ⊢ e₃ ≣ e₁ → size L₃ e₃ > n * size L₁ e₁
  go e₃ e₃≅e₁ with L₃→L₂ A e₃ (L₂≽L₃ e₃)
  go e₃ e₃≅e₁ | e₂ , e₂≅e₃ , e₂≤e₃ =
    begin-strict
      n * size L₁ e₁
    <⟨ ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
      (begin-strict
        m * (n * size L₁ e₁)
      ≡⟨ ℕ.*-assoc m n (size L₁ e₁) ⟨
        m * n * size L₁ e₁
      <⟨ e₁< e₂ (≅-trans e₂≅e₃ e₃≅e₁) ⟩
        size L₂ e₂
      ≤⟨ e₂≤e₃ ⟩
        m * size L₃ e₃
      ∎)
    ⟩
      size L₃ e₃
    ∎
    where
    open ℕ.≤-Reasoning

<ₛ-≤ₛ-transitive : {L₁ L₂ L₃ : SizedLang V} → Lang L₁ ≽ Lang L₂ → Lang L₂ ≋ Lang L₃ → L₁ <ₛ L₂ → L₂ ≤ₛ L₃ → L₁ <ₛ L₃
<ₛ-≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≋L₃@(L₂≽L₃ , _) (L₁≤ₛL₂ , L₂≰ₛL₁) L₂≤ₛL₃ .proj₁ = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
<ₛ-≤ₛ-transitive {L₁} {L₂} {L₃} L₁≽L₂ L₂≋L₃@(L₂≽L₃ , _) (L₁≤ₛL₂ , L₂≰ₛL₁) L₂≤ₛL₃ .proj₂ = ≱ₛ-≤ₛ-transitive L₂≋L₃ L₂≰ₛL₁ L₂≤ₛL₃

<ₛ-transitive : {L₁ L₂ L₃ : SizedLang V} → Lang L₁ ≽ Lang L₂ → Lang L₂ ≋ Lang L₃ → L₁ <ₛ L₂ → L₂ <ₛ L₃ → L₁ <ₛ L₃
<ₛ-transitive L₁≽L₂ L₂≋L₃ L₁<ₛL₂ L₂<ₛL₃ = <ₛ-≤ₛ-transitive L₁≽L₂ L₂≋L₃ L₁<ₛL₂ (<ₛ→≤ₛ L₂<ₛL₃)

<ₛ-irreflexive : {L₁ L₂ : SizedLang V} → L₁ =ₛ L₂ → ¬ (L₁ <ₛ L₂)
<ₛ-irreflexive {L₁} {L₂} (L₁≤ₛL₂ , (n , L₁→L₂)) (L₁≤ₛL₂' , L₂≰ₛL₁) with L₂≰ₛL₁ n
<ₛ-irreflexive {L₁} {L₂} (L₁≤ₛL₂ , (n , L₁→L₂)) (L₁≤ₛL₂' , L₂≰ₛL₁) | A , e₁ , e₁-translatable , e₂< with L₁→L₂ A e₁ e₁-translatable
<ₛ-irreflexive {L₁} {L₂} (L₁≤ₛL₂ , (n , L₁→L₂)) (L₁≤ₛL₂' , L₂≰ₛL₁) | A , e₁ , e₁-translatable , e₁< | e₂ , e₁≅e₂ , e₂≤e₁ = ℕ.n≮n (size L₂ e₂) (ℕ.≤-trans (ℕ.s≤s e₂≤e₁) (e₁< e₂ e₁≅e₂))

<ₛ-Respectsʳ : {L₁ L₂ L₃ : SizedLang V} → Lang L₁ ≋ Lang L₂ → Lang L₂ ≋ Lang L₃ → L₂ =ₛ L₃ → L₁ <ₛ L₂ → L₁ <ₛ L₃
<ₛ-Respectsʳ {L₁} {L₂} {L₃} (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂) (L₂≤ₛL₃@(m , L₃→L₂) , L₃≤ₛL₂) (L₁≤ₛL₂ , L₂≰ₛL₁) .proj₁ = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
<ₛ-Respectsʳ {L₁} {L₂} {L₃} (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂) (L₂≤ₛL₃@(m , L₃→L₂) , L₃≤ₛL₂) (L₁≤ₛL₂ , L₂≰ₛL₁) .proj₂ n with L₂≰ₛL₁ (m * n)
<ₛ-Respectsʳ {L₁} {L₂} {L₃} (L₁≽L₂ , L₂≽L₁) (L₂≽L₃ , L₃≽L₂) (L₂≤ₛL₃@(m , L₃→L₂) , L₃≤ₛL₂) (L₁≤ₛL₂ , L₂≰ₛL₁) .proj₂ n | A , e₁ , e₁-translatable , e₁<
  = A , e₁ , (≽-trans L₃≽L₂ L₂≽L₁) e₁ , go
  where
  go : (e₃ : Expression (Lang L₃) A) → Lang L₃ , Lang L₁ ⊢ e₃ ≣ e₁ → size L₃ e₃ > n * size L₁ e₁
  go e₃ e₃≅e₁ with L₃→L₂ A e₃ (L₂≽L₃ e₃)
  go e₃ e₃≅e₁ | e₂ , e₂≅e₃ , e₂≤e₃ = ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
    (begin-strict
      m * (n * size L₁ e₁)
    ≡⟨ ℕ.*-assoc m n (size L₁ e₁) ⟨
      m * n * size L₁ e₁
    <⟨ ℕ.≤-trans (e₁< e₂ (≅-trans e₂≅e₃ e₃≅e₁)) e₂≤e₃ ⟩
      m * size L₃ e₃
    ∎)
    where
    open ℕ.≤-Reasoning

<ₛ-Respectsˡ : {L₁ L₂ L₃ : SizedLang V} → Lang L₃ ≋ Lang L₂ → Lang L₂ ≋ Lang L₁ → L₂ =ₛ L₃ → L₂ <ₛ L₁ → L₃ <ₛ L₁
<ₛ-Respectsˡ {L₁} {L₂} {L₃} (L₃≽L₂ , L₂≽L₃) (L₂≽L₁ , L₁≽L₂) (L₂≤ₛL₃ , L₃≤ₛL₂@(m , L₂→L₃)) (L₂≤ₛL₁ , L₁≰ₛL₂) .proj₁ = ≤ₛ-transitive L₃≽L₂ L₂≽L₁ L₃≤ₛL₂ L₂≤ₛL₁
<ₛ-Respectsˡ {L₁} {L₂} {L₃} (L₃≽L₂ , L₂≽L₃) (L₂≽L₁ , L₁≽L₂) (L₂≤ₛL₃ , L₃≤ₛL₂@(m , L₂→L₃)) (L₂≤ₛL₁ , L₁≰ₛL₂) .proj₂ n with L₁≰ₛL₂ (m * n)
<ₛ-Respectsˡ {L₁} {L₂} {L₃} (L₃≽L₂ , L₂≽L₃) (L₂≽L₁ , L₁≽L₂) (L₂≤ₛL₃ , L₃≤ₛL₂@(m , L₂→L₃)) (L₂≤ₛL₁ , L₁≰ₛL₂) .proj₂ n | A , e₂ , e₂-translatable , e₂< with L₂→L₃ A e₂ (L₃≽L₂ e₂)
<ₛ-Respectsˡ {L₁} {L₂} {L₃} (L₃≽L₂ , L₂≽L₃) (L₂≽L₁ , L₁≽L₂) (L₂≤ₛL₃ , L₃≤ₛL₂@(m , L₂→L₃)) (L₂≤ₛL₁ , L₁≰ₛL₂) .proj₂ n | A , e₂ , e₂-translatable , e₂< | e₃ , e₃≅e₂ , e₃≤e₂
  = A , e₃ , (≽-trans L₁≽L₂ L₂≽L₃) e₃ , go
  where
  go : (e₁ : Expression (Lang L₁) A) → Lang L₁ , Lang L₃ ⊢ e₁ ≣ e₃ → size L₁ e₁ > n * size L₃ e₃
  go e₁ e₁≅e₃ =
    begin-strict
      n * size L₃ e₃
    ≤⟨ ℕ.*-monoʳ-≤ n e₃≤e₂ ⟩
      n * (m * size L₂ e₂)
    ≡⟨ ℕ.*-assoc n m (size L₂ e₂) ⟨
      n * m * size L₂ e₂
    ≡⟨ Eq.cong (_* size L₂ e₂) (ℕ.*-comm n m) ⟩
      m * n * size L₂ e₂
    <⟨ e₂< e₁ (≅-trans e₁≅e₃ e₃≅e₂) ⟩
      size L₁ e₁
    ∎
    where
    open ℕ.≤-Reasoning


_<ₛ[_]_
  : (L₁ : SizedLang V)
  → (f : ℕ → ℕ)
  → (L₂ : SizedLang V)
  → Set _
L₁ <ₛ[ f ] L₂ = L₁ ≤ₛ L₂ × L₂ ≰ₛ[ f ] L₁

<ₛ[]-growthFactor : {L₁ L₂ : SizedLang V} (f : ℕ → ℕ) → L₁ <ₛ[ f ] L₂ → ℕ
<ₛ[]-growthFactor f = proj₁ ∘ proj₁

≤ₛ[]-<ₛ[]-transitive
  : {L₁ L₂ L₃ : SizedLang V}
  → (f : ℕ → ℕ)
  → monotonic f
  → Lang L₁ ≽ Lang L₂
  → Lang L₂ ≋ Lang L₃
  → (L₁≤ₛL₂ : L₁ ≤ₛ L₂)
  → L₂ <ₛ[ (λ n → f (≤ₛ[]-growthFactor id L₁≤ₛL₂ * n)) ] L₃
  → L₁ <ₛ[ f ] L₃
≤ₛ[]-<ₛ[]-transitive {L₁} {L₂} {L₃} f f-monotone L₁≽L₂ (L₂≽L₃ , L₃≽L₂) L₁≤ₛL₂@(m , L₂→L₁) (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₁ = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
≤ₛ[]-<ₛ[]-transitive {L₁} {L₂} {L₃} f f-monotone L₁≽L₂ L₂≽L₃ L₁≤ₛL₂@(m , L₂→L₁) (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₂ n with L₃≰ₛL₂ n
≤ₛ[]-<ₛ[]-transitive {L₁} {L₂} {L₃} f f-monotone L₁≽L₂ L₂≽L₃ L₁≤ₛL₂@(m , L₂→L₁) (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₂ n | A , e₂ , (e₃ , e₂≅e₃) , e₂< with L₂→L₁ A e₂ (L₁≽L₂ e₂)
≤ₛ[]-<ₛ[]-transitive {L₁} {L₂} {L₃} f f-monotone L₁≽L₂ L₂≽L₃ L₁≤ₛL₂@(m , L₂→L₁) (L₂≤ₛL₃ , L₃≰ₛL₂) .proj₂ n | A , e₂ , (e₃ , e₂≅e₃) , e₂< | e₁ , e₁≅e₂ , e₁≤e₂
  = A , e₁ , (e₃ , ≅-trans e₁≅e₂ e₂≅e₃) , λ e₃' e₃≅e₁ →
    begin-strict
      n * f (size L₁ e₁)
    ≤⟨ ℕ.*-monoʳ-≤ n (f-monotone (e₁≤e₂)) ⟩
      n * f (m * size L₂ e₂)
    <⟨ e₂< e₃' (≅-trans e₃≅e₁ e₁≅e₂) ⟩
      size L₃ e₃'
    ∎
  where
  open ℕ.≤-Reasoning

<ₛ[]-≤ₛ[]-transitive
  : {L₁ L₂ L₃ : SizedLang V}
  → (f : ℕ → ℕ)
  → Lang L₁ ≽ Lang L₂
  → Lang L₂ ≋ Lang L₃
  → L₁ <ₛ[ f ] L₂
  → L₂ ≤ₛ L₃
  → L₁ <ₛ[ f ] L₃
<ₛ[]-≤ₛ[]-transitive {L₁} {L₂} {L₃} f L₁≽L₂ (L₂≽L₃ , L₃≽L₂) (L₁≤ₛL₂ , L₂≰ₛL₁) L₂≤ₛL₃@(m , L₃→L₂) .proj₁ = ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
<ₛ[]-≤ₛ[]-transitive {L₁} {L₂} {L₃} f L₁≽L₂ (L₂≽L₃ , L₃≽L₂) (L₁≤ₛL₂ , L₂≰ₛL₁) L₂≤ₛL₃@(m , L₃→L₂) .proj₂ n with L₂≰ₛL₁ (m * n)
<ₛ[]-≤ₛ[]-transitive {L₁} {L₂} {L₃} f L₁≽L₂ (L₂≽L₃ , L₃≽L₂) (L₁≤ₛL₂ , L₂≰ₛL₁) L₂≤ₛL₃@(m , L₃→L₂) .proj₂ n | A , e₁ , (e₂ , e₁≅e₂) , e₁<
  = A , e₁ , Product.map₂ (≅-trans e₁≅e₂) (L₃≽L₂ e₂) , go
  where
  go : (e₃ : Expression (Lang L₃) A) → Lang L₃ , Lang L₁ ⊢ e₃ ≣ e₁ → size L₃ e₃ > n * f (size L₁ e₁)
  go e₃ e₃≅e₁ with L₃→L₂ A e₃ (L₂≽L₃ e₃)
  go e₃ e₃≅e₁ | e₂ , e₂≅e₃ , e₂≤e₃ =
    begin-strict
      n * f (size L₁ e₁)
    <⟨ ℕ.*-cancelˡ-< m (n * f (size L₁ e₁)) (size L₃ e₃)
      (begin-strict
        m * (n * f (size L₁ e₁))
      ≡⟨ ℕ.*-assoc m n (f (size L₁ e₁)) ⟨
        m * n * f (size L₁ e₁)
      <⟨ e₁< e₂ (≅-trans e₂≅e₃ e₃≅e₁) ⟩
        size L₂ e₂
      ≤⟨ e₂≤e₃ ⟩
        m * size L₃ e₃
      ∎)
    ⟩
      size L₃ e₃
    ∎
    where
    open ℕ.≤-Reasoning


_=ₛ'_ : SizedLang V → SizedLang V → Set₁
L₁ =ₛ' L₂ = Lang L₁ ≋ Lang L₂ × L₁ ≤ₛ L₂ × L₂ ≤ₛ L₁

_≤ₛ'_ : SizedLang V → SizedLang V → Set₁
L₁ ≤ₛ' L₂ = Lang L₁ ≽ Lang L₂ × L₁ ≤ₛ[ id ] L₂

_<ₛ'_ : SizedLang V → SizedLang V → Set₁
L₁ <ₛ' L₂ = Lang L₁ ≋ Lang L₂ × L₁ ≤ₛ L₂ × L₂ ≰ₛ L₁

=ₛ'-IsEquivalence : IsEquivalence _=ₛ'_
=ₛ'-IsEquivalence = record
  { refl = ≋-refl , =ₛ-reflexive
  ; sym = Product.map ≋-sym =ₛ-symmetric
  ; trans = λ (L₁≋L₂ , L₁=ₛL₂) (L₂≋L₃ , L₂=ₛL₃) → ≋-trans L₁≋L₂ L₂≋L₃ , =ₛ-transitive L₁≋L₂ L₂≋L₃ L₁=ₛL₂ L₂=ₛL₃
  }

≤ₛ'-IsPreOrder : IsPreorder _=ₛ'_ _≤ₛ'_
≤ₛ'-IsPreOrder = record
  { isEquivalence = =ₛ'-IsEquivalence
  ; reflexive = λ ((L₁≽L₂ , L₂≽L₁) , L₁≤ₛL₂) → L₁≽L₂ , ≤ₛ-reflexive L₁≤ₛL₂
  ; trans = λ (L₁≽L₂ , L₁≤ₛL₂) (L₂≽L₃ , L₂≤ₛL₃) → ≽-trans L₁≽L₂ L₂≽L₃ , ≤ₛ-transitive L₁≽L₂ L₂≽L₃ L₁≤ₛL₂ L₂≤ₛL₃
  }

≤ₛ'-IsPartialOrder : IsPartialOrder _=ₛ'_ _≤ₛ'_
≤ₛ'-IsPartialOrder = record
  { isPreorder = ≤ₛ'-IsPreOrder
  ; antisym = λ (L₁≽L₂ , L₁≤ₛL₂) (L₂≽L₁ , L₂≤ₛL₁) → (L₁≽L₂ , L₂≽L₁) , ≤ₛ-antisymmetric L₁≤ₛL₂ L₂≤ₛL₁
  }

<ₛ'-IsStrictPartialOrder : IsStrictPartialOrder _=ₛ'_ _<ₛ'_
<ₛ'-IsStrictPartialOrder = record
  { isEquivalence = =ₛ'-IsEquivalence
  ; trans = λ (L₁≋L₂@(L₁≽L₂ , L₂≽L₁) , L₁≤ₛL₂) (L₂≋L₃ , L₂≤ₛL₃) → ≋-trans L₁≋L₂ L₂≋L₃ , <ₛ-transitive L₁≽L₂ L₂≋L₃ L₁≤ₛL₂ L₂≤ₛL₃
  ; irrefl = λ (L₁≋L₂ , L₁=ₛL₂) (L₁≋L₂ , L₁<ₛL₂) → <ₛ-irreflexive L₁=ₛL₂ L₁<ₛL₂
  ; <-resp-≈ =
      (λ (L₂≋L₃ , L₂=ₛL₃) (L₁≋L₂ , L₁<ₛL₂) → ≋-trans L₁≋L₂ L₂≋L₃ , <ₛ-Respectsʳ L₁≋L₂ L₂≋L₃ L₂=ₛL₃ L₁<ₛL₂)
    , (λ (L₁≋L₂ , L₁=ₛL₂) (L₁≋L₃ , L₁<ₛL₃) → ≋-trans (≋-sym L₁≋L₂) L₁≋L₃ , <ₛ-Respectsˡ (≋-sym L₁≋L₂) L₁≋L₃ L₁=ₛL₂ L₁<ₛL₃)
  }


=ₛ'→=ₛ : {L₁ L₂ : SizedLang V} → L₁ =ₛ' L₂ → L₁ =ₛ L₂
=ₛ'→=ₛ = proj₂

≤ₛ'→≤ₛ : {L₁ L₂ : SizedLang V} → L₁ =ₛ' L₂ → L₁ =ₛ L₂
≤ₛ'→≤ₛ = proj₂

<ₛ'→<ₛ : {L₁ L₂ : SizedLang V} → L₁ =ₛ' L₂ → L₁ =ₛ L₂
<ₛ'→<ₛ = proj₂


≰→¬≤ : {L₁ L₂ : SizedLang V} → L₁ ≰ₛ L₂ → ¬ (L₁ ≤ₛ L₂)
≰→¬≤ {L₁} {L₂} L₁≰ₛL₂ (n , L₁→L₂) with L₁≰ₛL₂ n
≰→¬≤ {L₁} {L₂} L₁≰ₛL₂ (n , L₁→L₂) | A , e₂ , e₂-translatable , e₂< with L₁→L₂ A e₂ e₂-translatable
≰→¬≤ {L₁} {L₂} L₁≰ₛL₂ (n , L₁→L₂) | A , e₂ , e₂-translatable , e₂< | e₁ , e₂≅e₁ , e₁≤e₂ = ℕ.n≮n (size L₁ e₁) (ℕ.≤-trans (ℕ.s≤s e₁≤e₂) (e₂< e₁ e₂≅e₁))

≤→¬≰ : {L₁ L₂ : SizedLang V} → L₁ ≤ₛ L₂ → ¬ (L₁ ≰ₛ L₂)
≤→¬≰ {L₁} {L₂} (n , L₂→L₁) L₂≰ₛL₁ with L₂≰ₛL₁ n
≤→¬≰ {L₁} {L₂} (n , L₂→L₁) L₂≰ₛL₁ | A , e₂ , e₂-translatable , e₂< with L₂→L₁ A e₂ e₂-translatable
≤→¬≰ {L₁} {L₂} (n , L₂→L₁) L₂≰ₛL₁ | A , e₂ , e₂-translatable , e₂< | e₁ , e₂≅e₁ , e₁≤e₂ = ℕ.n≮n (n * size L₂ e₂) (ℕ.≤-trans (e₂< e₁ e₂≅e₁) e₁≤e₂)

≰→¬= : {L₁ L₂ : SizedLang V} → L₁ ≰ₛ L₂ → ¬ (L₁ =ₛ L₂)
≰→¬= L₁≰ₛL₂ (L₁≤ₛL₂ , L₂≤ₛL₁) = ≰→¬≤ L₁≰ₛL₂ L₁≤ₛL₂

≤→Compiler : {L₁ L₂ : SizedLang V} → Lang L₁ ≽ Lang L₂ → L₁ ≤ₛ L₂ → LanguageCompiler (Lang L₂) (Lang L₁)
≤→Compiler L₁≽L₂ (n , L₂→L₁) = record
  { compile = λ {A} e₂ → proj₁ (L₂→L₁ A e₂ (L₁≽L₂ e₂))
  ; config-compiler = λ {A} e₂ → record
    { to = ⊆-index (proj₂ (proj₁ (proj₂ (L₂→L₁ A e₂ (L₁≽L₂ e₂)))))
    ; from = ⊆-index (proj₁ (proj₁ (proj₂ (L₂→L₁ A e₂ (L₁≽L₂ e₂)))))
    }
  ; preserves = λ {A} e₂ → ≅→≅[] (≅-sym (proj₁ (proj₂ (L₂→L₁ A e₂ (L₁≽L₂ e₂)))))
  }

≤ₛ-weakening : ∀ {L₁ L₂ : SizedLang V} {f g : ℕ → ℕ} → f ∈ 𝒪[ g ] → L₁ ≤ₛ[ f ] L₂ → L₁ ≤ₛ[ g ] L₂
≤ₛ-weakening {L₁} {L₂} {f} {g} (m , f≤g) (n , L₂→L₁) .proj₁ = n * m
≤ₛ-weakening {L₁} {L₂} {f} {g} (m , f≤g) (n , L₂→L₁) .proj₂ A e₂ e₂-translatable with L₂→L₁ A e₂ e₂-translatable
≤ₛ-weakening {L₁} {L₂} {f} {g} (m , f≤g) (n , L₂→L₁) .proj₂ A e₂ e₂-translatable | e₁ , e₁≅e₂ , e₂≤e₁ = e₁ , e₁≅e₂ , (
  begin
    size L₁ e₁
  ≤⟨ e₂≤e₁ ⟩
    n * f (size L₂ e₂)
  ≤⟨ ℕ.*-monoʳ-≤ n (f≤g (size L₂ e₂)) ⟩
    n * (m * g (size L₂ e₂))
  ≡⟨ ℕ.*-assoc n m (g (size L₂ e₂)) ⟨
    n * m * g (size L₂ e₂)
  ∎)
  where
  open ℕ.≤-Reasoning

≰ₛ-strengthening : ∀ {L₁ L₂ : SizedLang V} {f g : ℕ → ℕ} → f ∈ 𝒪[ g ] → L₁ ≰ₛ[ g ] L₂ → L₁ ≰ₛ[ f ] L₂
≰ₛ-strengthening {L₁} {L₂} {f} {g} (m , f≤g) L₁≰ₛL₂ n with L₁≰ₛL₂ (n * m)
... | A , e₂ , e₂-translatable , >e₂ = A , e₂ , e₂-translatable , λ e₁ e₁≅e₂ →
  begin-strict
    n * f (size L₂ e₂)
  ≤⟨ ℕ.*-monoʳ-≤ n (f≤g (size L₂ e₂)) ⟩
    n * (m * g (size L₂ e₂))
  ≡⟨ ℕ.*-assoc n m (g (size L₂ e₂)) ⟨
    (n * m) * g (size L₂ e₂)
  <⟨ >e₂ e₁ e₁≅e₂ ⟩
    size L₁ e₁
  ∎
  where
  open ℕ.≤-Reasoning

open Axiom.ExcludedMiddle using (ExcludedMiddle)
open Axiom.DoubleNegationElimination using (em⇒dne)
module Classical (excludedMiddle : ∀ {ℓ} → ExcludedMiddle ℓ) where
  ¬∀→∃¬ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} → ¬ (∀ (a : A) → P a) → Σ[ a ∈ A ] ¬ P a
  ¬∀→∃¬ {A = A} {P = P} ¬∀P with excludedMiddle {P = Σ[ a ∈ A ] ¬ P a}
  ¬∀→∃¬ {A = A} {P = P} ¬∀P | yes ∃P = ∃P
  ¬∀→∃¬ {A = A} {P = P} ¬∀P | no ∄P = ⊥-elim (¬∀P (λ a → em⇒dne excludedMiddle (¬∃⟶∀¬ ∄P a)))

  map-∀ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {P : A → Set ℓ₂} {Q : A → Set ℓ₃}
    → (∀ {a} → P a → Q a) → (∀ (a : A) → P a) → (∀ (a : A) → Q a)
  map-∀ f ∀P a = f (∀P a)

  map-Σ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {P : A → Set ℓ₂} {Q : A → Set ℓ₃}
    → (∀ {a} → P a → Q a) → Σ[ a ∈ A ] P a → Σ[ a ∈ A ] Q a
  map-Σ f (a , Pa) = a , f Pa

  ¬∀→∃ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {P : A → Set ℓ₂} {Q : A → Set ℓ₃} → (∀ {a : A} → ¬ P a → Q a) → ¬ (∀ (a : A) → P a) → Σ[ a ∈ A ] Q a
  ¬∀→∃ f P = map-Σ f (¬∀→∃¬ P)

  ¬∃→∀ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {P : A → Set ℓ₂} {Q : A → Set ℓ₃} → (∀ {a : A} → ¬ P a → Q a) → ¬ (Σ[ a ∈ A ] P a) → ∀ (a : A) → Q a
  ¬∃→∀ f P = map-∀ f (¬∃⟶∀¬ P)

  ¬≤→≰ : {L₁ L₂ : SizedLang V} → ¬ (L₁ ≤ₛ L₂) → L₁ ≰ₛ L₂
  ¬≤→≰ = ¬∃→∀ (¬∀→∃ (¬∀→∃ (¬∀→∃ (¬∃→∀ (¬∃→∀ ℕ.≰⇒>)))))

  ¬≰→≤ : {L₁ L₂ : SizedLang V} → ¬ (L₁ ≰ₛ L₂) → L₁ ≤ₛ L₂
  ¬≰→≤ = ¬∀→∃ (¬∃→∀ (¬∃→∀ (¬∃→∀ (¬∀→∃ (¬∀→∃ ℕ.≮⇒≥)))))
