```agda
open import Framework.Definitions
module Framework.Relation.Expression (V : 𝕍) {A : 𝔸} where

open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans)
open import Function using (_∘_; Injective)

open import Framework.VariabilityLanguage

open import Data.EqIndexedSet using
  ( _⊆_; _≅_; _≐_
  ; ≐→≅
  ; ⊆-refl; ⊆-antisym; ⊆-trans
  ; ≅-refl;     ≅-sym; ≅-trans
  )
```

## Comparing expressions of the same language

Two expressions `e₁` , `e₂` of the same language are semantically equivalent
if the functions they describe are pointwise equal (same output for same inputs):
```agda
_⊢_≣₁_ : ∀ (L : VariabilityLanguage V)
  → (e₁ e₂ : Expression L A)
  → Set₁
L ⊢ e₁ ≣₁ e₂ = ⟦ e₁ ⟧ ≐ ⟦ e₂ ⟧
  where
    ⟦_⟧ = Semantics L
infix 5 _⊢_≣₁_

≣₁-IsEquivalence : ∀ {L : VariabilityLanguage V} → IsEquivalence (L ⊢_≣₁_)
≣₁-IsEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ x≣y c → sym (x≣y c)
  ; trans = λ i≣j j≣k c → trans (i≣j c) (j≣k c)
  }
```

Syntactic equality implies semantic equality, independent of the semantics:
```agda
≡→≣₁ : ∀ {L : VariabilityLanguage V} {a b : Expression L A}
  → a ≡ b
    ----------
  → L ⊢ a ≣₁ b
≡→≣₁ eq c rewrite eq = refl
```

## Comparing expressions across languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.

```agda
_,_⊢_≤_ :
  ∀ (L₁ L₂ : VariabilityLanguage V)
  → Expression L₁ A
  → Expression L₂ A
  → Set₁
L₁ , L₂ ⊢ e₁ ≤ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂
infix 5 _,_⊢_≤_

_,_⊢_≣_ :
  ∀ (L₁ L₂ : VariabilityLanguage V)
  → Expression L₁ A
  → Expression L₂ A
  → Set₁
L₁ , L₂ ⊢ e₁ ≣ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = Semantics L₁
    ⟦_⟧₂ = Semantics L₂
infix 5 _,_⊢_≣_

≤-refl : ∀ (L : VariabilityLanguage V) (e : Expression L A)
  → L , L ⊢ e ≤ e
≤-refl _ _ = ⊆-refl

≤-antisym : ∀ {L M : VariabilityLanguage V} {a : Expression L A} {b : Expression M A}
  → L , M ⊢ a ≤ b
  → M , L ⊢ b ≤ a
  → L , M ⊢ a ≣ b
≤-antisym = ⊆-antisym

≤-trans : ∀ {L M N : VariabilityLanguage V}
            {a : Expression L A} {b : Expression M A} {c : Expression N A}
  → L , M ⊢ a ≤ b
  → M , N ⊢ b ≤ c
    -------------
  → L , N ⊢ a ≤ c
≤-trans = ⊆-trans

≣-refl : ∀ (L : VariabilityLanguage V) (e : Expression L A)
    -------------
  → L , L ⊢ e ≣ e
≣-refl _ _ = ≅-refl

≣-sym : ∀ {L M : VariabilityLanguage V} {a : Expression L A} {b : Expression M A}
  → L , M ⊢ a ≣ b
  → M , L ⊢ b ≣ a
≣-sym = ≅-sym

≣-trans : ∀ {L M N : VariabilityLanguage V}
            {a : Expression L A} {b : Expression M A} {c : Expression N A}
  → L , M ⊢ a ≣ b
  → M , N ⊢ b ≣ c
    -------------
  → L , N ⊢ a ≣ c
≣-trans = ≅-trans

≣₁→≣ : ∀ {L : VariabilityLanguage V} {a b : Expression L A}
  → L ⊢ a ≣₁ b
  → L , L ⊢ a ≣ b
≣₁→≣ = ≐→≅
```
