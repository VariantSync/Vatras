open import Vatras.Framework.Definitions using (𝔸; 𝕍)
module Vatras.Succinctness.ProofDefinition (V : 𝕍) where

open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; _≤_; _>_; _<_; _*_)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)
open import Size using (∞)

open import Vatras.Data.EqIndexedSet using (≅-refl; ≅-sym; ≅-trans; ≅→≅[]; ⊆-index)
open import Vatras.Framework.Relation.Expression V using (_,_⊢_≣_)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; Expression)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Succinctness.Sizes using (SizedLang; Lang; size)

_≤Size_ : SizedLang V → SizedLang V → Set₁
L₁ ≤Size L₂ =
  Σ[ n ∈ ℕ ]
  ∀ (A : 𝔸) →
  ∀ (e₂ : Expression (Lang L₂) A) →
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
      Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
    × size L₁ e₁ ≤ n * size L₂ e₂

_=Size_ : SizedLang V → SizedLang V → Set₁
L₁ =Size L₂ = L₁ ≤Size L₂ × L₂ ≤Size L₁

_≱Size_ : SizedLang V → SizedLang V → Set₁
L₁ ≱Size L₂ =
  ∀ (n : ℕ) →
  Σ[ A ∈ 𝔸 ]
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
  ∀ (e₂ : Expression (Lang L₂) A )
  → Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
  → size L₂ e₂ > n * size L₁ e₁

_<Size_ : SizedLang V → SizedLang V → Set₁
L₁ <Size L₂ = L₁ ≤Size L₂ × L₁ ≱Size L₂


≤Size-refl : {L : SizedLang V} → L ≤Size L
≤Size-refl {L} = 1 , λ A e → e , ≅-refl , ℕ.≤-reflexive (Eq.sym (ℕ.*-identityˡ (size L e)))

≤Size-reflexive : {L₁ L₂ : SizedLang V} → L₁ =Size L₂ → L₁ ≤Size L₂
≤Size-reflexive (L₁≤L₂ , L₂≤L₁) = L₁≤L₂

≤Size-transitive : {L₁ L₂ L₃ : SizedLang V} → L₁ ≤Size L₂ → L₂ ≤Size L₃ → L₁ ≤Size L₃
≤Size-transitive {L₁} {L₂} {L₃} (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₁ = n₁ * n₂
≤Size-transitive {L₁} {L₂} {L₃} (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ with L₃→L₂ A e₃
≤Size-transitive {L₁} {L₂} {L₃} (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ | e₂ , e₂≅e₃ , e₁≤e₂ with L₂→L₁ A e₂
≤Size-transitive {L₁} {L₂} {L₃} (n₁ , L₂→L₁) (n₂ , L₃→L₂) .proj₂ A e₃ | e₂ , e₂≅e₃ , e₂≤e₃ | e₁ , e₁≅e₂ , e₁≤e₂ = e₁ , ≅-trans e₁≅e₂ e₂≅e₃ ,
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

≤Size-antisymmetric : {L₁ L₂ : SizedLang V} → L₁ ≤Size L₂ → L₂ ≤Size L₁ → L₁ =Size L₂
≤Size-antisymmetric L₁≤L₂ L₂≤L₁ = L₁≤L₂ , L₂≤L₁


=Size-reflexive : {L : SizedLang V} → L =Size L
=Size-reflexive = ≤Size-refl , ≤Size-refl

=Size-symmetric : {L₁ L₂ : SizedLang V} → L₁ =Size L₂ → L₂ =Size L₁
=Size-symmetric (L₁≤L₂ , L₂≤L₁) = L₂≤L₁ , L₁≤L₂

=Size-transitive : {L₁ L₂ L₃ : SizedLang V} → L₁ =Size L₂ → L₂ =Size L₃ → L₁ =Size L₃
=Size-transitive (L₁≤L₂ , L₂≤L₁) (L₂≤L₃ , L₃≤L₂) = ≤Size-transitive L₁≤L₂ L₂≤L₃ , ≤Size-transitive L₃≤L₂ L₂≤L₁

<Size-transitive : {L₁ L₂ L₃ : SizedLang V} → L₁ <Size L₂ → L₂ <Size L₃ → L₁ <Size L₃
<Size-transitive {L₁} {L₂} {L₃} (L₁≤L₂ , L₁≱L₂) (L₂≤L₃@(m , L₃→L₂) , L₂≱L₃) .proj₁ = ≤Size-transitive L₁≤L₂ L₂≤L₃
<Size-transitive {L₁} {L₂} {L₃} (L₁≤L₂ , L₁≱L₂) (L₂≤L₃@(m , L₃→L₂) , L₂≱L₃) .proj₂ n with L₁≱L₂ (m * n)
<Size-transitive {L₁} {L₂} {L₃} (L₁≤L₂ , L₁≱L₂) (L₂≤L₃@(m , L₃→L₂) , L₂≱L₃) .proj₂ n | A , e₁ , e₁< = A , e₁ , go
  where
  go : (e₃ : Expression (Lang L₃) A) → Lang L₁ , Lang L₃ ⊢ e₁ ≣ e₃ → size L₃ e₃ > n * size L₁ e₁
  go e₃ e₁≅e₃ with L₃→L₂ A e₃
  go e₃ e₁≅e₃ | e₂ , e₂≅e₃ , e₂≤e₃ =
    begin-strict
      n * size L₁ e₁
    <⟨ ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
      (begin
        ℕ.suc (m * (n * size L₁ e₁))
      ≡⟨ Eq.cong ℕ.suc (ℕ.*-assoc m n (size L₁ e₁)) ⟨
        ℕ.suc (m * n * size L₁ e₁)
      ≤⟨ ℕ.≤-trans (e₁< e₂ (≅-trans e₁≅e₃ (≅-sym e₂≅e₃))) e₂≤e₃ ⟩
        m * size L₃ e₃
      ∎)
    ⟩
      size L₃ e₃
    ∎
    where
    open ℕ.≤-Reasoning

<Size-irreflexive : {L₁ L₂ : SizedLang V} → L₁ =Size L₂ → ¬ (L₁ <Size L₂)
<Size-irreflexive {L₁} {L₂} (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) with L₁≱L₂ n
<Size-irreflexive {L₁} {L₂} (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) | A , e₁ , e₂< with L₁→L₂ A e₁
<Size-irreflexive {L₁} {L₂} (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) | A , e₁ , e₁< | e₂ , e₂≅e₁ , e₂≤e₁ = ℕ.n≮n (size L₂ e₂) (ℕ.≤-trans (ℕ.s≤s e₂≤e₁) (e₁< e₂ (≅-sym e₂≅e₁)))

<Size-Respectsʳ : {L₁ L₂ L₃ : SizedLang V} → L₂ =Size L₃ → L₁ <Size L₂ → L₁ <Size L₃
<Size-Respectsʳ {L₁} {L₂} {L₃} (L₂≤L₃@(m , L₃→L₂) , L₃≤L₂) (L₁≤L₂ , L₁≱L₂) .proj₁ = ≤Size-transitive L₁≤L₂ L₂≤L₃
<Size-Respectsʳ {L₁} {L₂} {L₃} (L₂≤L₃@(m , L₃→L₂) , L₃≤L₂) (L₁≤L₂ , L₁≱L₂) .proj₂ n with L₁≱L₂ (m * n)
<Size-Respectsʳ {L₁} {L₂} {L₃} (L₂≤L₃@(m , L₃→L₂) , L₃≤L₂) (L₁≤L₂ , L₁≱L₂) .proj₂ n | A , e₁ , e₁< = A , e₁ , go
  where
  go : (e₃ : Expression (Lang L₃) A) → Lang L₁ , Lang L₃ ⊢ e₁ ≣ e₃ → size L₃ e₃ > n * size L₁ e₁
  go e₃ e₁≅e₃ with L₃→L₂ A e₃
  go e₃ e₁≅e₃ | e₂ , e₂≅e₃ , e₂≤e₃ = ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
    (begin
      ℕ.suc (m * (n * size L₁ e₁))
    ≡⟨ Eq.cong ℕ.suc (ℕ.*-assoc m n (size L₁ e₁)) ⟨
      ℕ.suc (m * n * size L₁ e₁)
    ≤⟨ ℕ.≤-trans (e₁< e₂ (≅-trans e₁≅e₃ (≅-sym e₂≅e₃))) e₂≤e₃ ⟩
      m * size L₃ e₃
    ∎)
    where
    open ℕ.≤-Reasoning

<Size-Respectsˡ : {L₁ L₂ L₃ : SizedLang V} → L₂ =Size L₃ → L₂ <Size L₁ → L₃ <Size L₁
<Size-Respectsˡ {L₁} {L₂} {L₃} (L₂≤L₃ , L₃≤L₂@(m , L₂→L₃)) (L₂≤L₁ , L₂≱L₁) .proj₁ = ≤Size-transitive L₃≤L₂ L₂≤L₁
<Size-Respectsˡ {L₁} {L₂} {L₃} (L₂≤L₃ , L₃≤L₂@(m , L₂→L₃)) (L₂≤L₁ , L₂≱L₁) .proj₂ n with L₂≱L₁ (m * n)
<Size-Respectsˡ {L₁} {L₂} {L₃} (L₂≤L₃ , L₃≤L₂@(m , L₂→L₃)) (L₂≤L₁ , L₂≱L₁) .proj₂ n | A , e₂ , e₂< with L₂→L₃ A e₂
<Size-Respectsˡ {L₁} {L₂} {L₃} (L₂≤L₃ , L₃≤L₂@(m , L₂→L₃)) (L₂≤L₁ , L₂≱L₁) .proj₂ n | A , e₂ , e₂< | e₃ , e₃≅e₂ , e₃≤e₂ = A , e₃ , go
  where
  go : (e₁ : Expression (Lang L₁) A) → Lang L₃ , Lang L₁ ⊢ e₃ ≣ e₁ → size L₁ e₁ > n * size L₃ e₃
  go e₁ e₃≅e₁ =
    begin-strict
      n * size L₃ e₃
    ≤⟨ ℕ.*-monoʳ-≤ n e₃≤e₂ ⟩
      n * (m * size L₂ e₂)
    ≡⟨ ℕ.*-assoc n m (size L₂ e₂) ⟨
      n * m * size L₂ e₂
    ≡⟨ Eq.cong (_* size L₂ e₂) (ℕ.*-comm n m) ⟩
      m * n * size L₂ e₂
    <⟨ e₂< e₁ (≅-trans (≅-sym e₃≅e₂) e₃≅e₁) ⟩
      size L₁ e₁
    ∎
    where
    open ℕ.≤-Reasoning


=Size-IsEquivalence : IsEquivalence _=Size_
=Size-IsEquivalence = record
  { refl = =Size-reflexive
  ; sym = =Size-symmetric
  ; trans = =Size-transitive
  }

≤Size-IsPreOrder : IsPreorder _=Size_ _≤Size_
≤Size-IsPreOrder = record
  { isEquivalence = =Size-IsEquivalence
  ; reflexive = ≤Size-reflexive
  ; trans = ≤Size-transitive
  }

≤Size-IsPartialOrder : IsPartialOrder _=Size_ _≤Size_
≤Size-IsPartialOrder = record
  { isPreorder = ≤Size-IsPreOrder
  ; antisym = ≤Size-antisymmetric
  }

<Size-IsStrictPartialOrder : IsStrictPartialOrder _=Size_ _<Size_
<Size-IsStrictPartialOrder = record
  { isEquivalence = =Size-IsEquivalence
  ; trans = <Size-transitive
  ; irrefl = <Size-irreflexive
  ; <-resp-≈ = <Size-Respectsʳ , <Size-Respectsˡ
  }


<Size→≤Size : {L₁ L₂ : SizedLang V} → L₁ <Size L₂ → L₁ ≤Size L₂
<Size→≤Size (L₁≤L₂ , L₁≱L₂) = L₁≤L₂

≱→¬≤ : {L₁ L₂ : SizedLang V} → L₁ ≱Size L₂ → ¬ (L₂ ≤Size L₁)
≱→¬≤ {L₁} {L₂} L₁≱L₂ (n , L₁→L₂) with L₁≱L₂ n
≱→¬≤ {L₁} {L₂} L₁≱L₂ (n , L₁→L₂) | A , e₁ , e₁< with L₁→L₂ A e₁
≱→¬≤ {L₁} {L₂} L₁≱L₂ (n , L₁→L₂) | A , e₁ , e₁< | e₂ , e₂≅e₁ , e₂≤e₁ = ℕ.n≮n (size L₂ e₂) (ℕ.≤-trans (ℕ.s≤s e₂≤e₁) (e₁< e₂ (≅-sym e₂≅e₁)))

≱→¬= : {L₁ L₂ : SizedLang V} → L₁ ≱Size L₂ → ¬ (L₁ =Size L₂)
≱→¬= L₁≠L₂ (L₁≤L₂ , L₂≤L₁) = ≱→¬≤ L₁≠L₂ L₂≤L₁

≤→¬≱ : {L₁ L₂ : SizedLang V} → L₁ ≤Size L₂ → ¬ (L₂ ≱Size L₁)
≤→¬≱ {L₁} {L₂} (n , L₂→L₁) L₂≱L₁ with L₂≱L₁ n
≤→¬≱ {L₁} {L₂} (n , L₂→L₁) L₂≱L₁ | A , e₂ , e₂< with L₂→L₁ A e₂
≤→¬≱ {L₁} {L₂} (n , L₂→L₁) L₂≱L₁ | A , e₂ , e₂< | e₁ , e₂≅e₁ , e₁≤e₂ = ℕ.n≮n (n * size L₂ e₂) (ℕ.≤-trans (e₂< e₁ (≅-sym e₂≅e₁)) e₁≤e₂)

≤→Compiler : {L₁ L₂ : SizedLang V} → L₁ ≤Size L₂ → LanguageCompiler (Lang L₂) (Lang L₁)
≤→Compiler (n , e₂→e₁) = record
  { compile = λ {A} e₂ → proj₁ (e₂→e₁ A e₂)
  ; config-compiler = λ {A} e₂ → record
    { to = ⊆-index (proj₂ (proj₁ (proj₂ (e₂→e₁ A e₂))))
    ; from = ⊆-index (proj₁ (proj₁ (proj₂ (e₂→e₁ A e₂))))
    }
  ; preserves = λ {A} e₂ → ≅→≅[] (≅-sym (proj₁ (proj₂ (e₂→e₁ A e₂))))
  }

¬Compiler→¬≤ : {L₁ L₂ : SizedLang V} → ¬ LanguageCompiler (Lang L₁) (Lang L₂) → ¬ L₂ ≤Size L₁
¬Compiler→¬≤ ¬Compiler L₂≤L₁ = ¬Compiler (≤→Compiler L₂≤L₁)

¬Compiler→≤ : {L₁ L₂ : SizedLang V} → {A : 𝔸} → (e₂ : Expression (Lang L₂) A) → (∀ (e₁ : Expression (Lang L₁) A) → ¬ Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂) → L₂ ≱Size L₁
¬Compiler→≤ {A = A} e₂ e₁≇e₂ n = A , e₂ , λ e₁ e₂≅e₁ → ⊥-elim (e₁≇e₂ e₁ (≅-sym e₂≅e₁))


translatable
  : (VL₁ VL₂ : SizedLang V)
  → {A : 𝔸}
  → (e₁ : Expression (Lang VL₁) A)
  → Set _
translatable VL₁ VL₂ {A} e₁ =
  Σ[ e₂ ∈ Expression (Lang VL₂) A ]
  Lang VL₂ , Lang VL₁ ⊢ e₂ ≣ e₁

simplification
  : (f : ℕ → ℕ)
  → (VL₁ VL₂ : SizedLang V)
  → Set _
simplification f VL₁ VL₂ =
  ∀ (A : 𝔸) →
  Σ[ m ∈ ℕ ]
  ∀ (e₂ : Expression (Lang VL₂) A)
  → translatable VL₂ VL₁ e₂
  → Σ[ e₁ ∈ Expression (Lang VL₁) A ]
      (Lang VL₁ , Lang VL₂ ⊢ e₁ ≣ e₂)
    × size VL₁ e₁ ≤ m * f (size VL₂ e₂)
