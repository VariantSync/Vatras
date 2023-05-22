```agda
{-# OPTIONS --sized-types #-}

open import Definitions

module Relations.Semantic where
```

# Relations of Variability Languages

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Size using (Size)

open import Data.Product   using (_,_; ∃-syntax; Σ-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size)

open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)
open import Relation.Binary using (Rel; IsEquivalence)
open import Level using (0ℓ; suc)

open import Relations.GeneralizedEquivalence using (iseq)

open import Relation.Nullary.Negation using (¬_)

import Data.Multiset as MSet
```

## Semantic Relations of Expressions Within a Single Language

We consider three kinds of semantic relations between two expressions `a` and `b` in the same language:
- Subset `a ⊆ b` **iff** `a` describes a subset of the variants described by `b`.
- Variant equivalence `a ≚ b` **iff** `a` and `b` describe the same set of variants (i.e., `a ⊆ b` and `b ⊆ a`)
- Semantic equivalence `a ≈ b` **iff** `a` and `b` are variant equivalent and same configurations yield same variants.

We start with semantic equivalence because it is the easiest to define.
Any two expressions `a` and `b` in a variability language `L` are equivalent if their semantics `⟦_⟧` are equivalent:
```agda
_≣_ : ∀ {A : Domain} {L : VariabilityLanguage}
  → (e₁ e₂ : Expression A L)
  → Set
_≣_ {L = L} e₁ e₂ = ⟦ get e₁ ⟧ ≡ ⟦ get e₂ ⟧
  where ⟦_⟧ = semantics L
infix 5 _≣_

-- for syntax
_⊢_≣_ : ∀ {i j : Size} {A : Domain}
  → (L : VariabilityLanguage)
  → expression L i A
  → expression L j A
  → Set
L ⊢ e₁ ≣ e₂ = fromExpression L e₁ ≣ fromExpression L e₂
infix 5 _⊢_≣_
```
A proposition `L , ⟦_⟧ ⊢ e₁ ≈ e₂` reads as, in a language `L` with semantics `⟦_⟧` the expressions `e₁` and `e₂` are semantically equivalent, i.e., `⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧`.

Semantic equivalence `≈` inherits all properties from structural equality `≡` because it is just an alias. In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence (e.g., as stated in the choice calculus TOSEM paper).

Obviously, syntactic equality (or rather structural equality) implies semantic equality, independent of the semantics:
```agda
≡→≣ : ∀ {i : Size} {A : Domain} {L : VariabilityLanguage} {a b : expression L i A}
  → a ≡ b
    --------------
  → L ⊢ a ≣ b
≡→≣ eq rewrite eq = refl
```

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence. Each variant that can be derived from the first expression, can also be derived from the second expression and vice versa. We thus first describe the variant-subset relation `⊆` and then define variant-equality as a bi-directional subset.
```agda
-- _,_⊢_⊆ᵥ_ : ∀ {i j : Size} {F : FeatureLang} {S : SelectionLang} {A : Domain}
--   → (L : VarLang)
--   → Semantics L F S
--   → L i A
--   → L j A
--   → Set
-- L , ⟦_⟧ ⊢ e₁ ⊆ᵥ e₂ = ⟦ e₁ ⟧ ⊆ ⟦ e₂ ⟧ --∀ (c₁ : C) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
-- infix 5 _,_⊢_⊆ᵥ_

-- _,_⊢_≚_ : ∀ {i j : Size} {F : FeatureLang} {S : SelectionLang} {A : Domain}
--   → (L : VarLang)
--   → Semantics L F S
--   → L i A
--   → L j A
--   → Set
-- L , s ⊢ e₁ ≚ e₂ =
--     (L , s ⊢ e₁ ⊆ᵥ e₂)
--   × (L , s ⊢ e₂ ⊆ᵥ e₁)
-- infix 5 _,_⊢_≚_
```
A proposition `L , ⟦_⟧ ⊢ e₁ ⊆ e₂` reads as, in a language `L` with semantics `⟦_⟧` the expression `e₁` describes a subset of the variants described by `e₂`.

```agda
-- ⊆ᵥ-refl : ∀ {i : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {S : Semantics L F S} {e : L i A}
--     ---------------
--   → L , S ⊢ e ⊆ᵥ e
-- ⊆ᵥ-refl = ⊆-refl

-- ⊆ᵥ-antisym : ∀ {i j : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {S : Semantics L F S} {e₁ : L i A} {e₂ : L j A}
--   → L , S ⊢ e₁ ⊆ᵥ e₂
--   → L , S ⊢ e₂ ⊆ᵥ e₁
--     -----------------
--   → L , S ⊢ e₁ ≚ e₂
-- ⊆ᵥ-antisym = ⊆-antisym

-- ⊆ᵥ-trans : ∀ {i j k : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {S : Semantics L F S} {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
--   → L , S ⊢ e₁ ⊆ᵥ e₂
--   → L , S ⊢ e₂ ⊆ᵥ e₃
--     -----------------
--   → L , S ⊢ e₁ ⊆ᵥ e₃
-- ⊆ᵥ-trans = ⊆-trans

-- ≚-refl : ∀ {i : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {S : Semantics L F S} {e : L i A}
--     --------------
--   → L , S ⊢ e ≚ e
-- ≚-refl {i} {A} {L} {C} {S} {e} =
--     ⊆ᵥ-refl {i} {A} {L} {C} {S} {e}
--   , ⊆ᵥ-refl {i} {A} {L} {C} {S} {e}

-- ≚-sym : ∀ {i j : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {e₁ : L i A} {e₂ : L j A} {S : Semantics L F S}
--   → L , S ⊢ e₁ ≚ e₂
--     ----------------
--   → L , S ⊢ e₂ ≚ e₁
-- ≚-sym (e₁⊆e₂ , e₂⊆e₁) = e₂⊆e₁ , e₁⊆e₂

-- ≚-trans : ∀ {i j k : Size} {A : Domain} {L : VarLang} {F : FeatureLang} {S : SelectionLang} {S : Semantics L F S} {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
--   → L , S ⊢ e₁ ≚ e₂
--   → L , S ⊢ e₂ ≚ e₃
--     ----------------
--   → L , S ⊢ e₁ ≚ e₃
-- ≚-trans     {i} {j} {k} {A} {L} {C} {S} {e₁} {e₂} {e₃} (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂) =
--     ⊆ᵥ-trans {i} {j} {k} {A} {L} {C} {S} {e₁} {e₂} {e₃} e₁⊆e₂ e₂⊆e₃
--   , ⊆ᵥ-trans {k} {j} {i} {A} {L} {C} {S} {e₃} {e₂} {e₁} e₃⊆e₂ e₂⊆e₁
```

## Semantic Relations of Different Languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.
Finally, we formalize translations between languages and show that creating translations allows us to conclude certain relations between languages.

### Relating Expressions

First we generalize `_,_⊢_⊆_` and `_,_⊢_≚_` from single languages to two different languages.
This step is straighforward as it just requires us to introduce additional parameters for the second language and reformulating the right-hand side of relations to refer to the second language.
The main insight here is that we can compare expressions across languages because they share the same semantic domain: variants.
```agda
_⊆ᵥ_ : ∀ {A : Domain} → IRel (Expression A) 0ℓ
_⊆ᵥ_ {A} {L₁} {L₂} e₁ e₂ = ⟦ get e₁ ⟧₁ ⊆ ⟦ get e₂ ⟧₂
  where
    ⟦_⟧₁ = semantics L₁
    ⟦_⟧₂ = semantics L₂
    open MSet (VariantSetoid _ A) using (_⊆_)
infix 5 _⊆ᵥ_

_≚_ : ∀ {A : Domain} → IRel (Expression A) 0ℓ
e₁ ≚ e₂ = e₁ ⊆ᵥ e₂ × e₂ ⊆ᵥ e₁
infix 5 _≚_

≚-isIndexedEquivalence : ∀ {A : Domain} → IsIndexedEquivalence (Expression A) _≚_
≚-isIndexedEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }
  where open MSet (VariantSetoid _ _) using (≅-refl; ≅-sym; ≅-trans)

≚-isEquivalence : ∀ {A : Domain} {L : VariabilityLanguage} → IsEquivalence {suc 0ℓ} (_≚_ {A} {L})
≚-isEquivalence = iseq ≚-isIndexedEquivalence
```

We introduce some aliases for the above relations that have a more readable syntax when used with concrete expressions:
```agda
_,_⊢_⊆ᵥ_ : ∀ {A : Domain} {i j : Size} → (L₁ L₂ : VariabilityLanguage) → expression L₁ i A → expression L₂ j A → Set
L₁ , L₂ ⊢ e₁ ⊆ᵥ e₂ = fromExpression L₁ e₁ ⊆ᵥ fromExpression L₂ e₂
infix 5 _,_⊢_⊆ᵥ_

_,_⊢_≚_ : ∀ {A : Domain} {i j : Size} → (L₁ L₂ : VariabilityLanguage) → expression L₁ i A → expression L₂ j A → Set
L₁ , L₂ ⊢ e₁ ≚ e₂ = fromExpression L₁ e₁ ≚ fromExpression L₂ e₂
infix 5 _,_⊢_≚_
```

In the following the prove the same properties as for the relations within a single language. The proofs are identical:
```agda
≚→≅ : ∀ {A : Domain} {L₁ L₂ : VariabilityLanguage} {e₁ : Expression A L₁} {e₂ : Expression A L₂}
  → e₁ ≚ e₂
    ---------------------------------------------------
  → (let open MSet (VariantSetoid _ A) using (_≅_)
         ⟦_⟧₁ = semantics L₁
         ⟦_⟧₂ = semantics L₂
      in ⟦ get e₁ ⟧₁ ≅ ⟦ get e₂ ⟧₂)
≚→≅ (fst , snd) = fst , snd
```

Semantic equality implies variant equality:
```agda
≣→⊆ᵥ : ∀ {A : Domain} {L : VariabilityLanguage} {a b : Expression A L}
  → a ≣ b
    -------
  → a ⊆ᵥ b
-- From a≈b, we know that ⟦ a ⟧ ≡ ⟦ b ⟧. To prove subset, we have to show that both sides produce the same variant for a given configuration. We do so by applying the configuration to both sides of the equation of a≈b.
≣→⊆ᵥ a≈b c rewrite a≈b = c , refl

≣→≚ : ∀ {A : Domain} {L : VariabilityLanguage} {a b : Expression A L}
  → a ≣ b
    -------
  → a ≚ b
≣→≚     {A} {L} {a} {b} a≣b =
    ≣→⊆ᵥ {A} {L} {a} {b} a≣b
  , ≣→⊆ᵥ {A} {L} {b} {a} (Eq.sym a≣b)
```

### Relating Languages

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
```agda
-- L₁ ⊇ L₂
_is-at-least-as-expressive-as_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-at-least-as-expressive-as L₂ =
  ∀ {A : Domain} (e₂ : Expression A L₂) →
      (Σ[ e₁ ∈ Expression A L₁ ]
        (e₂ ≚ e₁))
  -- TODO: Somehow rephrase it like this:
  -- (semantics L₂) ⊆ (semantics L₁)
  -- where open MSet (Variant A) ≚-isEquivalence using (_⊆_)
  --where open MSet (Expression A) ≚-isEquivalence using (_⊆_)

-- ¬ (L₂ ⊇ L₁)
_is-less-expressive-than_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-less-expressive-than L₂ = ¬ (L₁ is-at-least-as-expressive-as L₂)

-- L₁ ⊃ L₂ ⇔ L₁ ⊇ L₂ ∧ ¬ (L₂ ⊇ L₁)
_is-more-expressive-than_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-more-expressive-than L₂ =
    L₁ is-at-least-as-expressive-as L₂
  × L₂ is-less-expressive-than L₁
```

A language `L₁` is variant equivalent to another language `L₂` **iff** they are equally expressive. This means that we can translate between both languages. (We cannot prove the existence of a translation though because we cannot find a translation automatically. We use the inverse route, concluding propositions about languages from building translations later.)
```agda
_is-variant-equivalent-to_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-variant-equivalent-to L₂ =
    (L₁ is-at-least-as-expressive-as L₂)
  × (L₂ is-at-least-as-expressive-as L₁)
```

Expressiveness is transitive:
```agda
-- trans-expressiveness : ∀ {L₁ L₂ L₃ : VariabilityLanguage}
--   → L₁ is-at-least-as-expressive-as L₂
--   → L₂ is-at-least-as-expressive-as L₃
--     ----------------------------------
--   → L₁ is-at-least-as-expressive-as L₃
-- trans-expressiveness
--   {L₁} {L₂} {L₃}
--   L₂→L₁ L₃→L₂ {i₃} {A} e₃
--   =
--   let i₂ , e₂ , e₃≚e₂ = L₃→L₂ e₃
--       i₁ , e₁ , e₂≚e₁ = L₂→L₁ e₂
--    in
--       i₁ , e₁ ,
--         ≚-trans'
--           {i₃} {i₂} {i₁}
--           {A}
--           {L₃} {L₂} {L₁}
--           {C₃} {C₂} {C₁}
--           {S₃} {S₂} {S₁}
--           e₃≚e₂ e₂≚e₁
```

