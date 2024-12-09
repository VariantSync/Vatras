open import Vatras.Framework.Definitions using (𝔸)
module Vatras.SyntacticExpressiveness (A : 𝔸) where

open import Data.Nat as ℕ using (ℕ; _≤_; _>_; _<_; _*_)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)
open import Size using (∞)

open import Vatras.Data.EqIndexedSet using (≅-refl; ≅-sym; ≅-trans)
open import Vatras.Framework.Variants using (Rose)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; Expression)

record SizedLang : Set₂ where
  field
    Lang : VariabilityLanguage (Rose ∞)
    size : Expression Lang A → ℕ
open SizedLang

_≤Size_ : SizedLang → SizedLang → Set₁
L₁ ≤Size L₂ =
  Σ[ n ∈ ℕ ]
  ∀ (e₂ : Expression (Lang L₂) A) →
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
      Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
    × size L₁ e₁ ≤ n * size L₂ e₂

_=Size_ : SizedLang → SizedLang → Set₁
L₁ =Size L₂ = L₁ ≤Size L₂ × L₂ ≤Size L₁

_≱Size_ : SizedLang → SizedLang → Set₁
L₁ ≱Size L₂ =
  ∀ (n : ℕ) →
  Σ[ e₁ ∈ Expression (Lang L₁) A ]
  ∀ (e₂ : Expression (Lang L₂) A )
  → Lang L₁ , Lang L₂ ⊢ e₁ ≣ e₂
  → size L₂ e₂ > n * size L₁ e₁

_<Size_ : SizedLang → SizedLang → Set₁
L₁ <Size L₂ = L₁ ≤Size L₂ × L₁ ≱Size L₂


≤Size-refl : (L : SizedLang) → L ≤Size L
≤Size-refl L = 1 , λ e → e , ≅-refl , ℕ.≤-reflexive (Eq.sym (ℕ.*-identityˡ (size L e)))

≤Size-reflexive : (L₁ L₂ : SizedLang) → L₁ =Size L₂ → L₁ ≤Size L₂
≤Size-reflexive L₁ L₂ (L₁≤L₂ , L₂≤L₁) = L₁≤L₂

≤Size-transitive : (L₁ L₂ L₃ : SizedLang) → L₁ ≤Size L₂ → L₂ ≤Size L₃ → L₁ ≤Size L₃
≤Size-transitive L₁ L₂ L₃ (n₁ , L₂→L₁) (n₂ , L₃→L₂) = n₁ * n₂ , go
  where
  open ℕ.≤-Reasoning

  go : (e₃ : Expression (Lang L₃) A) → Σ[ e₁ ∈ Expression (Lang L₁) A ] Lang L₁ , Lang L₃ ⊢ e₁ ≣ e₃ × size L₁ e₁ ≤ n₁ * n₂ * size L₃ e₃
  go e₃ with L₃→L₂ e₃
  go e₃ | e₂ , e₂≅e₃ , e₁≤e₂ with L₂→L₁ e₂
  go e₃ | e₂ , e₂≅e₃ , e₂≤e₃ | e₁ , e₁≅e₂ , e₁≤e₂ = e₁ , ≅-trans e₁≅e₂ e₂≅e₃ ,
    (begin
      size L₁ e₁
    ≤⟨ e₁≤e₂ ⟩
      n₁ * size L₂ e₂
    ≤⟨ ℕ.*-monoʳ-≤ n₁ e₂≤e₃ ⟩
      n₁ * (n₂ * size L₃ e₃)
    ≡⟨ ℕ.*-assoc n₁ n₂ (size L₃ e₃) ⟨
      n₁ * n₂ * size L₃ e₃
    ∎)

≤Size-antisymmetric : (L₁ L₂ : SizedLang) → L₁ ≤Size L₂ → L₂ ≤Size L₁ → L₁ =Size L₂
≤Size-antisymmetric L₁ L₂ L₁≤L₂ L₂≤L₁ = L₁≤L₂ , L₂≤L₁


=Size-reflexive : (L : SizedLang) → L =Size L
=Size-reflexive L = ≤Size-refl L , ≤Size-refl L

=Size-symmetric : (L₁ L₂ : SizedLang) → L₁ =Size L₂ → L₂ =Size L₁
=Size-symmetric L₁ L₂ (L₁≤L₂ , L₂≤L₁) = L₂≤L₁ , L₁≤L₂

=Size-transitive : (L₁ L₂ L₃ : SizedLang) → L₁ =Size L₂ → L₂ =Size L₃ → L₁ =Size L₃
=Size-transitive L₁ L₂ L₃ (L₁≤L₂ , L₂≤L₁) (L₂≤L₃ , L₃≤L₂) = ≤Size-transitive L₁ L₂ L₃ L₁≤L₂ L₂≤L₃ , ≤Size-transitive L₃ L₂ L₁ L₃≤L₂ L₂≤L₁

<Size-transitive : (L₁ L₂ L₃ : SizedLang) → L₁ <Size L₂ → L₂ <Size L₃ → L₁ <Size L₃
<Size-transitive L₁ L₂ L₃ (L₁≤L₂ , L₁≱L₂) (L₂≤L₃ , L₂≱L₃)
  = ≤Size-transitive L₁ L₂ L₃ L₁≤L₂ L₂≤L₃ , λ n → proj₁ (L₁≱L₂ (m * n)) , λ e₃ e₁≅e₃ → go n e₃ e₁≅e₃
  where
  m : ℕ
  m = proj₁ L₂≤L₃

  go : (n : ℕ) → (e₃ : Expression (Lang L₃) A) → Lang L₁ , Lang L₃ ⊢ proj₁ (L₁≱L₂ (m * n)) ≣ e₃ → size L₃ e₃ > n * size L₁ (proj₁ (L₁≱L₂ (m * n)))
  go n e₃ e₁≅e₃ =
    begin-strict
      n * size L₁ e₁
    <⟨ ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
      (begin
        ℕ.suc (m * (n * size L₁ e₁))
      ≡⟨ Eq.cong ℕ.suc (ℕ.*-assoc m n (size L₁ e₁)) ⟨
        ℕ.suc (m * n * size L₁ e₁)
      ≤⟨ ℕ.≤-trans e₂<e₁ e₂≤e₃ ⟩
        m * size L₃ e₃
      ∎)
    ⟩
      size L₃ e₃
    ∎
    where
    open ℕ.≤-Reasoning

    e₁ : Expression (Lang L₁) A
    e₁ = proj₁ (L₁≱L₂ (m * n))
    e₂ : Expression (Lang L₂) A
    e₂ = proj₁ (proj₂ L₂≤L₃ e₃)

    e₂≅e₃ : Lang L₂ , Lang L₃ ⊢ e₂ ≣ e₃
    e₂≅e₃ = proj₁ (proj₂ (proj₂ L₂≤L₃ e₃))

    e₂≤e₃ : size L₂ e₂ ≤ m * size L₃ e₃
    e₂≤e₃ = proj₂ (proj₂ (proj₂ L₂≤L₃ e₃))

    e₂<e₁ : m * n * size L₁ e₁ < size L₂ e₂
    e₂<e₁ = proj₂ (L₁≱L₂ (m * n)) e₂ (≅-trans e₁≅e₃ (≅-sym e₂≅e₃))

<Size-irreflexive : (L₁ L₂ : SizedLang) → L₁ =Size L₂ → ¬ (L₁ <Size L₂)
<Size-irreflexive L₁ L₂ (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) with L₁≱L₂ n
<Size-irreflexive L₁ L₂ (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) | e₁ , e₂< with L₁→L₂ e₁
<Size-irreflexive L₁ L₂ (L₁≤L₂ , (n , L₁→L₂)) (L₁≤L₂' , L₁≱L₂) | e₁ , e₁< | e₂ , e₂≅e₁ , e₂≤e₁ = ℕ.n≮n (size L₂ e₂) (ℕ.≤-trans (ℕ.s≤s e₂≤e₁) (e₁< e₂ (≅-sym e₂≅e₁)))

<Size-Respectsʳ : (L₁ L₂ L₃ : SizedLang) → L₂ =Size L₃ → L₁ <Size L₂ → L₁ <Size L₃
<Size-Respectsʳ L₁ L₂ L₃ (L₂≤L₃@(m , L₃→L₂) , L₃≤L₂) (L₁≤L₂ , L₁≱L₂) = ≤Size-transitive L₁ L₂ L₃ L₁≤L₂ L₂≤L₃ , λ n → proj₁ (L₁≱L₂ (m * n)) , λ e₃ e₁≅e₃ → go n e₃ e₁≅e₃
  where
  go : ∀ (n : ℕ) (e₃ : Expression (Lang L₃) A) → Lang L₁ , Lang L₃ ⊢ proj₁ (L₁≱L₂ (m * n)) ≣ e₃ → size L₃ e₃ > n * size L₁ (proj₁ (L₁≱L₂ (m * n)))
  go n e₃ e₁≅e₃ = ℕ.*-cancelˡ-< m (n * size L₁ e₁) (size L₃ e₃)
    (begin
      ℕ.suc (m * (n * size L₁ e₁))
    ≡⟨ Eq.cong ℕ.suc (ℕ.*-assoc m n (size L₁ e₁)) ⟨
      ℕ.suc (m * n * size L₁ e₁)
    ≤⟨ ℕ.≤-trans e₁<e₂ e₂≤e₃ ⟩
      m * size L₃ e₃
    ∎)
    where
    open ℕ.≤-Reasoning

    e₁ : Expression (Lang L₁) A
    e₁ = proj₁ (L₁≱L₂ (m * n))
    e₂ : Expression (Lang L₂) A
    e₂ = proj₁ (L₃→L₂ e₃)

    e₂≅e₃ : Lang L₂ , Lang L₃ ⊢ e₂ ≣ e₃
    e₂≅e₃ = proj₁ (proj₂ (L₃→L₂ e₃))

    e₂≤e₃ : size L₂ e₂ ≤ m * size L₃ e₃
    e₂≤e₃ = proj₂ (proj₂ (L₃→L₂ e₃))
    e₁<e₂ : m * n * size L₁ e₁ < size L₂ e₂
    e₁<e₂ = proj₂ (L₁≱L₂ (m * n)) e₂ (≅-trans e₁≅e₃ (≅-sym e₂≅e₃))

<Size-Respectsˡ : (L₁ L₂ L₃ : SizedLang) → L₂ =Size L₃ → L₂ <Size L₁ → L₃ <Size L₁
<Size-Respectsˡ L₁ L₂ L₃ (L₂≤L₃ , L₃≤L₂@(m , L₂→L₃)) (L₂≤L₁ , L₂≱L₁) = ≤Size-transitive L₃ L₂ L₁ L₃≤L₂ L₂≤L₁ , λ n → proj₁ (L₂→L₃ (proj₁ (L₂≱L₁ (m * n)))) , λ e₁ e₃≅e₁ → go n e₁ e₃≅e₁
  where
  go : ∀ (n : ℕ) (e₁ : Expression (Lang L₁) A) → Lang L₃ , Lang L₁ ⊢ proj₁ (L₂→L₃ (proj₁ (L₂≱L₁ (m * n)))) ≣ e₁ → size L₁ e₁ > n * size L₃ (proj₁ (L₂→L₃ (proj₁ (L₂≱L₁ (m * n)))))
  go n e₁ e₃≅e₁ =
    begin-strict
      n * size L₃ e₃
    ≤⟨ ℕ.*-monoʳ-≤ n e₃≤e₂ ⟩
      n * (m * size L₂ e₂)
    ≡⟨ ℕ.*-assoc n m (size L₂ e₂) ⟨
      n * m * size L₂ e₂
    ≡⟨ Eq.cong (_* size L₂ e₂) (ℕ.*-comm n m) ⟩
      m * n * size L₂ e₂
    <⟨ e₂<e₁ ⟩
      size L₁ e₁
    ∎
    where
    open ℕ.≤-Reasoning

    e₂ : Expression (Lang L₂) A
    e₂ = proj₁ (L₂≱L₁ (m * n))
    e₃ : Expression (Lang L₃) A
    e₃ = proj₁ (L₂→L₃ e₂)

    e₃≅e₂ : Lang L₃ , Lang L₂ ⊢ e₃ ≣ e₂
    e₃≅e₂ = proj₁ (proj₂ (L₂→L₃ e₂))

    e₂<e₁ : m * n * size L₂ e₂ < size L₁ e₁
    e₂<e₁ = proj₂ (L₂≱L₁ (m * n)) e₁ (≅-trans (≅-sym e₃≅e₂) e₃≅e₁)
    e₃≤e₂ : size L₃ e₃ ≤ m * size L₂ e₂
    e₃≤e₂ = proj₂ (proj₂ (L₂→L₃ e₂))


=Size-IsEquivalence : IsEquivalence _=Size_
=Size-IsEquivalence = record
  { refl = λ {L₁} → =Size-reflexive L₁
  ; sym = λ {L₁} {L₂} → =Size-symmetric L₁ L₂
  ; trans = λ {L₁} {L₂} {L₃} → =Size-transitive L₁ L₂ L₃
  }

≤Size-IsPreOrder : IsPreorder _=Size_ _≤Size_
≤Size-IsPreOrder = record
  { isEquivalence = =Size-IsEquivalence
  ; reflexive = λ {L₁} {L₂} → ≤Size-reflexive L₁ L₂
  ; trans = λ {L₁} {L₂} {L₃} → ≤Size-transitive L₁ L₂ L₃
  }

≤Size-IsPartialOrder : IsPartialOrder _=Size_ _≤Size_
≤Size-IsPartialOrder = record
  { isPreorder = ≤Size-IsPreOrder
  ; antisym = λ {L₁} {L₂} → ≤Size-antisymmetric L₁ L₂
  }

<Size-IsStrictPartialOrder : IsStrictPartialOrder _=Size_ _<Size_
<Size-IsStrictPartialOrder = record
  { isEquivalence = =Size-IsEquivalence
  ; trans = λ {L₁} {L₂} {L₃} → <Size-transitive L₁ L₂ L₃
  ; irrefl = λ {L₁} {L₂} → <Size-irreflexive L₁ L₂
  ; <-resp-≈ = (λ {L₁} {L₂} {L₃} → <Size-Respectsʳ L₁ L₂ L₃) , λ {L₁} {L₂} {L₃} → <Size-Respectsˡ L₁ L₂ L₃
  }


<Size→≤Size : (L₁ L₂ : SizedLang) → L₁ <Size L₂ → L₁ ≤Size L₂
<Size→≤Size L₁ L₂ (L₁≤L₂ , L₁≱L₂) = L₁≤L₂

≱→¬≤ : (L₁ L₂ : SizedLang) → L₁ ≱Size L₂ → ¬ (L₂ ≤Size L₁)
≱→¬≤ L₁ L₂ L₁≱L₂ (n , L₁→L₂) with L₁≱L₂ n
≱→¬≤ L₁ L₂ L₁≱L₂ (n , L₁→L₂) | e₁ , e₁< with L₁→L₂ e₁
≱→¬≤ L₁ L₂ L₁≱L₂ (n , L₁→L₂) | e₁ , e₁< | e₂ , e₂≅e₁ , e₂≤e₁ = ℕ.n≮n (size L₂ e₂) (ℕ.≤-trans (ℕ.s≤s e₂≤e₁) (e₁< e₂ (≅-sym e₂≅e₁)))

≱→¬= : (L₁ L₂ : SizedLang) → L₁ ≱Size L₂ → ¬ (L₁ =Size L₂)
≱→¬= L₁ L₂ L₁≠L₂ (L₁≤L₂ , L₂≤L₁) = ≱→¬≤ L₁ L₂ L₁≠L₂ L₂≤L₁

≤→¬≱ : (L₁ L₂ : SizedLang) → L₁ ≤Size L₂ → ¬ (L₂ ≱Size L₁)
≤→¬≱ L₁ L₂ (n , L₂→L₁) L₂≱L₁ with L₂≱L₁ n
≤→¬≱ L₁ L₂ (n , L₂→L₁) L₂≱L₁ | e₂ , e₂< with L₂→L₁ e₂
≤→¬≱ L₁ L₂ (n , L₂→L₁) L₂≱L₁ | e₂ , e₂< | e₁ , e₂≅e₁ , e₁≤e₂ = ℕ.n≮n (n * size L₂ e₂) (ℕ.≤-trans (e₂< e₁ (≅-sym e₂≅e₁)) e₁≤e₂)
