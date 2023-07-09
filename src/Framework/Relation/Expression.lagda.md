```agda
{-# OPTIONS --sized-types #-}

module Framework.Relation.Expression where

open import Axioms.Extensionality using (extensionality)

open import Data.Product using (_,_; ∃-syntax; Σ-syntax; _×_)
open import Relation.Binary using (Rel; Symmetric; IsEquivalence; Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

open import Function using (_∘_; Congruent)
open import Level using (0ℓ; suc)
open import Size using (Size)

open import Framework.Definitions
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
_≣_ : ∀ {A : 𝔸} {L : VariabilityLanguage}
  → (e₁ e₂ : Expression A L)
  → Set
_≣_ {L = L} e₁ e₂ =
  let ⟦_⟧ = semantics L ∘ get
   in ⟦ e₁ ⟧ ≗ ⟦ e₂ ⟧
infix 5 _≣_

-- alias for syntax
_⊢_≣_ : ∀ {i j : Size} {A : 𝔸}
  → (L : VariabilityLanguage)
  → expression L i A
  → expression L j A
  → Set
L ⊢ e₁ ≣ e₂ = fromExpression L e₁ ≣ fromExpression L e₂
infix 5 _⊢_≣_
```

Semantic equivalence `≣` inherits all properties from structural equality `≡` because it is just an alias. In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence (e.g., as stated in the choice calculus TOSEM paper).
```agda
≣-IsEquivalence : ∀ {A L} → IsEquivalence (_≣_ {A} {L})
≣-IsEquivalence = record
  { refl  = λ _ → Eq.refl
  ; sym   = λ x≣y c → Eq.sym (x≣y c)
  ; trans = λ i≣j j≣k c → Eq.trans (i≣j c) (j≣k c)
  }

≣-congruent : ∀ {A L} → Congruent (_≣_ {A} {L}) _≡_ (semantics L ∘ get)
≣-congruent = extensionality
```

Obviously, syntactic equality (or rather structural equality) implies semantic equality, independent of the semantics:
```agda
≡→≣ : ∀ {i : Size} {A : 𝔸} {L : VariabilityLanguage} {a b : expression L i A}
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
_⊆ᵥ_ : ∀ {A : 𝔸} → IRel (Expression A) 0ℓ
_⊆ᵥ_ {A} {L₁} {L₂} e₁ e₂ = ⟦ e₁ ⟧₁ ⊆ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = semantics L₁ ∘ get
    ⟦_⟧₂ = semantics L₂ ∘ get
    open ISet (VariantSetoid _ A) using (_⊆_)
infix 5 _⊆ᵥ_

_≚_ : ∀ {A : 𝔸} → IRel (Expression A) 0ℓ
_≚_ {A} {L₁} {L₂} e₁ e₂ = ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂
  where
    ⟦_⟧₁ = semantics L₁ ∘ get
    ⟦_⟧₂ = semantics L₂ ∘ get
    open ISet (VariantSetoid _ A) using (_≅_)
infix 5 _≚_

≚-isIndexedEquivalence : ∀ {A : 𝔸} → IsIndexedEquivalence (Expression A) _≚_
≚-isIndexedEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }
  where open ISet (VariantSetoid _ _) using (≅-refl; ≅-sym; ≅-trans)

≚-isEquivalence : ∀ {A} {L} → IsEquivalence {suc 0ℓ} (_≚_ {A} {L})
≚-isEquivalence = unwrap-IndexedEquivalence ≚-isIndexedEquivalence

≚-setoid : 𝔸 → VariabilityLanguage → Setoid (suc 0ℓ) 0ℓ
≚-setoid A L = record
  { Carrier       = Expression A L
  ; _≈_           = _≚_
  ; isEquivalence = ≚-isEquivalence
  }

-- ≚-setoid2 : 𝔸 → VariabilityLanguage → VariabilityLanguage → Setoid (suc 0ℓ) 0ℓ
-- ≚-setoid2 A L₁ L₂ = record
--   { Carrier = Expression A L₁ × Expression A L₂
--   ; _≈_ = _≚_
--   ; isEquivalence = ≚-isEquivalence
--   }
```

We introduce some aliases for the above relations that have a more readable syntax when used with concrete expressions:
```agda
_,_⊢_⊆ᵥ_ : ∀ {A : 𝔸} {i j : Size} → (L₁ L₂ : VariabilityLanguage) → expression L₁ i A → expression L₂ j A → Set
L₁ , L₂ ⊢ e₁ ⊆ᵥ e₂ = fromExpression L₁ e₁ ⊆ᵥ fromExpression L₂ e₂
infix 5 _,_⊢_⊆ᵥ_

_,_⊢_≚_ : ∀ {A : 𝔸} {i j : Size} → (L₁ L₂ : VariabilityLanguage) → expression L₁ i A → expression L₂ j A → Set
L₁ , L₂ ⊢ e₁ ≚ e₂ = fromExpression L₁ e₁ ≚ fromExpression L₂ e₂
infix 5 _,_⊢_≚_
```

Given two variant-equivalent expressions from different languages, we can conclude that their semantics are isomorphic.
```agda
≚→≅ : ∀ {A : 𝔸} {L₁ L₂ : VariabilityLanguage} {e₁ : Expression A L₁} {e₂ : Expression A L₂}
  → e₁ ≚ e₂
    -----------------------------------------------
  → (let open ISet (VariantSetoid _ A) using (_≅_)
         ⟦_⟧₁ = semantics L₁ ∘ get
         ⟦_⟧₂ = semantics L₂ ∘ get
      in ⟦ e₁ ⟧₁ ≅ ⟦ e₂ ⟧₂)
≚→≅ (fst , snd) = fst , snd
```

Semantic equality implies variant equality:
```agda
≣→⊆ᵥ : ∀ {A : 𝔸} {L : VariabilityLanguage} {a b : Expression A L}
  → a ≣ b
    -------
  → a ⊆ᵥ b
≣→⊆ᵥ a≣b c rewrite a≣b c = c , refl

≣→≚ : ∀ {A : 𝔸} {L : VariabilityLanguage} {a b : Expression A L}
  → a ≣ b
    ------
  → a ≚ b
≣→≚     {A} {L} {a} {b} a≣b =
    ≣→⊆ᵥ {A} {L} {a} {b} a≣b
  , ≣→⊆ᵥ {A} {L} {b} {a} b≣a
  where b≣a : b ≣ a
        b≣a = IsEquivalence.sym (≣-IsEquivalence {A} {L}) a≣b
```
