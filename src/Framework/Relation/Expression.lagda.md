```agda
{-# OPTIONS --sized-types #-}

module Framework.Relation.Expression where

open import Axioms.Extensionality using (extensionality)

open import Data.Product using (_,_; ∃-syntax; Σ-syntax; _×_)
open import Relation.Binary using (Rel; Symmetric; IsEquivalence; Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

open import Function using (_∘_; flip; Congruent)
open import Level using (0ℓ; suc)
open import Size using (Size)

open import Framework.Definitions
open import Framework.Variant
open import Util.UnwrapIndexedEquivalence using (unwrap-IndexedEquivalence)
import Data.IndexedSet as ISet
```

# Relating Expressions of Variability Languages

## Semantic Relations of Expressions Within a Single Language

We consider three kinds of semantic relations between two expressions `a` and `b` in the same language:
- Subset `a ⊆ b` **iff** `a` describes a subset of the variants described by `b`.
- Variant equivalence `a ≚ b` **iff** `a` and `b` describe the same set of variants (i.e., `a ⊆ b` and `b ⊆ a`)
- Semantic equivalence `a ≈ b` **iff** `a` and `b` are variant equivalent and same configurations yield same variants.

We start with semantic equivalence because it is the easiest to define.
Any two expressions `a` and `b` in a variability language `L` are equivalent if their semantics `⟦_⟧` are equivalent:
```agda
_⊢_≣_ : ∀ {V S} (L : VariabilityLanguage V S)
  → {A : 𝔸}
  → Expression L A
  → Expression L A
  → Set
syn _ with-sem ⟦_⟧ ⊢ e₁ ≣ e₂ = ⟦ e₁ ⟧ ≗ ⟦ e₂ ⟧
infix 5 _⊢_≣_
```

Semantic equivalence `≣` inherits all properties from structural equality `≡` because it is just an alias. In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence (e.g., as stated in the choice calculus TOSEM paper).
```agda
≣-IsEquivalence : ∀ {V S A} {L : VariabilityLanguage V S} → IsEquivalence (_⊢_≣_ L {A})
≣-IsEquivalence = record
  { refl  = λ _ → Eq.refl
  ; sym   = λ x≣y c → Eq.sym (x≣y c)
  ; trans = λ i≣j j≣k c → Eq.trans (i≣j c) (j≣k c)
  }

≣-congruent : ∀ {V S A} {L : VariabilityLanguage V S} → Congruent (_⊢_≣_ L {A}) _≡_ (Semantics L)
≣-congruent = extensionality
```

Obviously, syntactic equality (or rather structural equality) implies semantic equality, independent of the semantics:
```agda
≡→≣ : ∀ {V S A} {L : VariabilityLanguage V S} {a b : Expression L A}
  → a ≡ b
    ----------
  → L ⊢ a ≣ b
≡→≣ eq c rewrite eq = refl
```

## Semantic Relations of Different Languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.
Finally, we formalize translations between languages and show that creating translations allows us to conclude certain relations between languages.

### Relating Expressions

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence. Each variant that can be derived from the first expression, can also be derived from the second expression and vice versa. We thus first describe the variant-subset relation `⊆ᵥ` and then define variant-equality `≚` as a bi-directional subset.
The main insight here is that we can compare expressions across languages because they share the same semantic domain: variants.
```agda
_,_⊢_⊆ᵥ_ : ∀ {V S₁ S₂ A}
  → (L₁ : VariabilityLanguage V S₁)
  → (L₂ : VariabilityLanguage V S₂)
  → Expression L₁ A → Expression L₂ A → Set
_,_⊢_⊆ᵥ_ {V} {_} {_} {A} (syn _ with-sem ⟦_⟧₁) (syn _ with-sem ⟦_⟧₂) e₁ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
  where open IVSet V A using (_⊆_)
infix 5 _,_⊢_⊆ᵥ_

_,_⊢_≚_ : ∀ {V S₁ S₂}
  → (L₁ : VariabilityLanguage V S₁)
  → (L₂ : VariabilityLanguage V S₂)
  → {A : 𝔸}
  → Expression L₁ A → Expression L₂ A → Set
_,_⊢_≚_ {V} (syn _ with-sem ⟦_⟧₁) (syn _ with-sem ⟦_⟧₂) {A} e₁ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
  where open IVSet V A using (_≅_)
infix 5 _,_⊢_≚_

-- _≚_ : ∀ {V S₁ S₂} {L₁ : VariabilityLanguage V S₁} {L₂ : VariabilityLanguage V S₂}
--   → {A : 𝔸}
--   → Expression L₁ A → Expression L₂ A → Set
-- _≚_ {_} {_} {_} {L₁} {L₂} e₁ e₂ = L₁ , L₂ ⊢ e₁ ≚ e₂
-- infix 5 _≚_

-- TODO: Uncomment
-- ≚-isIndexedEquivalence : ∀ {V A} → IsIndexedEquivalence (flip Expression A) _≚_
-- ≚-isIndexedEquivalence {V} {A} = record
--   { refl  = ≅-refl
--   ; sym   = ≅-sym
--   ; trans = ≅-trans
--   }
--   where open IVSet V A using (≅-refl; ≅-sym; ≅-trans)

-- ≚-isEquivalence : ∀ {V A}
  -- → IsIndexedEquivalence (flip Expression A) (_≚_ {V} {A = A})
-- ≚-isEquivalence = {!!} --unwrap-IndexedEquivalence ≚-isIndexedEquivalence

-- TODO: Uncomment
-- ≚-setoid : 𝔸 → VariabilityLanguage → Setoid (suc 0ℓ) 0ℓ
-- ≚-setoid A L = record
--   { Carrier       = Expression A L
--   ; _≈_           = _≚_
--   ; isEquivalence = ≚-isEquivalence
--   }
```

Semantic equality implies variant equality:
```agda
≣→⊆ᵥ : ∀ {V S A} {L : VariabilityLanguage V S} {a b : Expression L A}
  → L ⊢ a ≣ b
    --------------
  → L , L ⊢ a ⊆ᵥ b
≣→⊆ᵥ a≣b c rewrite a≣b c = c , refl

≣→≚ : ∀ {V S A} {L : VariabilityLanguage V S} {a b : Expression L A}
  → L ⊢ a ≣ b
    --------------
  → L , L ⊢ a ≚ b
≣→≚     {V} {S} {A} {L} {a} {b} a≣b =
    ≣→⊆ᵥ {V} {S} {A} {L} {a} {b} a≣b
  , ≣→⊆ᵥ {V} {S} {A} {L} {b} {a} b≣a
  where b≣a : L ⊢ b ≣ a
        b≣a = IsEquivalence.sym (≣-IsEquivalence {V} {S} {A} {L}) a≣b
```
