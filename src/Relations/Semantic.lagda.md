```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Framework.Definitions

module Relations.Semantic where
```

# Relations of Variability Languages

```agda
open import Axioms.Extensionality using (extensionality)

open import Data.Product   using (_,_; ∃-syntax; Σ-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size)

open import Relation.Binary using (Rel; Symmetric; IsEquivalence; Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Negation using (¬_)

open import Function using (_∘_; Congruent)
open import Level using (0ℓ; suc)
open import Size using (Size)

open import Relations.GeneralizedEquivalence using (iseq)
import Data.IndexedSet as ISet
```

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

## Equivalence of Configurations

Two configurations are equivalent for an expressionwhen they produce the same variants for all expressions.
```agda
_⊢_≣ᶜ_ : ∀ {A : 𝔸} {L : VariabilityLanguage}
  → Expression A L
  → (c₁ c₂ : configuration L)
  → Set
_⊢_≣ᶜ_ {L = L} e c₁ c₂ = ⟦e⟧ c₁ ≡ ⟦e⟧ c₂
  where ⟦e⟧ = semantics L {size e} (get e)
infix 5 _⊢_≣ᶜ_

≣ᶜ-IsEquivalence : ∀ {A L} → (e : Expression A L) → IsEquivalence ( e ⊢_≣ᶜ_)
≣ᶜ-IsEquivalence _ = record
  { refl  = Eq.refl
  ; sym   = Eq.sym
  ; trans = Eq.trans
  }

≣ᶜ-congruent : ∀ {A L} → (e : Expression A L) → Congruent (e ⊢_≣ᶜ_) _≡_ (semantics L (get e))
≣ᶜ-congruent _ e⊢x≣ᶜy = e⊢x≣ᶜy

≣ᶜ-setoid : ∀ {A} {L : VariabilityLanguage}
  → Expression A L
  → Setoid 0ℓ 0ℓ
≣ᶜ-setoid {A} {L} e = record
  { Carrier       = configuration L
  ; _≈_           = e ⊢_≣ᶜ_
  ; isEquivalence = ≣ᶜ-IsEquivalence e
  }
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
≚-isEquivalence = iseq ≚-isIndexedEquivalence

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

### Relating Languages

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
```agda
-- L₁ ⊇ L₂
_is-at-least-as-expressive-as_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-at-least-as-expressive-as L₂ =
  ∀ {A : 𝔸} (e₂ : Expression A L₂) →
      (Σ[ e₁ ∈ Expression A L₁ ]
        (e₂ ≚ e₁))
  -- It would be nice if we could rephrase expressiveness to (semantics L₂) ⊆ (semantics L₁) but I we have to generalize our multisets somehow first to allow keys in the source set.

-- ¬ (L₂ ⊇ L₁)
_is-less-expressive-than_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-less-expressive-than L₂ = ¬ (L₁ is-at-least-as-expressive-as L₂)

-- L₁ ⊃ L₂ ⇔ L₁ ⊇ L₂ ∧ ¬ (L₂ ⊇ L₁)
_is-more-expressive-than_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-more-expressive-than L₂ =
    L₁ is-at-least-as-expressive-as L₂
  × L₂ is-less-expressive-than L₁
```

A language `L₁` is equally expressive as another language `L₂` **iff** they are at least as expressive as each other.
```agda
_is-equally-expressive-as_ : VariabilityLanguage → VariabilityLanguage → Set₁
L₁ is-equally-expressive-as L₂ =
    (L₁ is-at-least-as-expressive-as L₂)
  × (L₂ is-at-least-as-expressive-as L₁)
```

Expressiveness forms a partial order:
```agda
refl-expressiveness' : ∀ {L₁ L₂ : VariabilityLanguage}
  → L₁ ≡ L₂
    ----------------------------------
  → L₁ is-at-least-as-expressive-as L₂
refl-expressiveness' {L₁} L₁≡L₂ e rewrite L₁≡L₂ = e , (λ i → i , refl) , (λ i → i , refl) -- TODO: Reuse other refl-proofs here

refl-expressiveness : ∀ {L : VariabilityLanguage}
    --------------------------------
  → L is-at-least-as-expressive-as L
refl-expressiveness = refl-expressiveness' refl

trans-expressiveness : ∀ {L₁ L₂ L₃ : VariabilityLanguage}
  → L₁ is-at-least-as-expressive-as L₂
  → L₂ is-at-least-as-expressive-as L₃
    ----------------------------------
  → L₁ is-at-least-as-expressive-as L₃
trans-expressiveness L₂→L₁ L₃→L₂ {A} e₃ =
  let open ISet (VariantSetoid _ A)
      e₂ , e₃≚e₂ = L₃→L₂ e₃
      e₁ , e₂≚e₁ = L₂→L₁ e₂
   in e₁ , ≅-trans e₃≚e₂ e₂≚e₁ -- This proof is highly similar to ≅-trans itself. Maybe we could indeed reuse here.

antisym-expressiveness : ∀ {L₁ L₂}
  → L₁ is-at-least-as-expressive-as L₂
  → L₂ is-at-least-as-expressive-as L₁
    ----------------------------------
  → L₁ is-equally-expressive-as L₂
antisym-expressiveness L₁≻L₂ L₂≻L₁ = L₁≻L₂ , L₂≻L₁
```

Variant-Equivalence is an equivalence relations:
```agda
sym-variant-equivalence : ∀ {L₁ L₂ : VariabilityLanguage}
  → L₁ is-equally-expressive-as L₂
    ------------------------------
  → L₂ is-equally-expressive-as L₁
sym-variant-equivalence (L₁≻L₂ , L₂≻L₁) = L₂≻L₁ , L₁≻L₂

trans-variant-equivalence : ∀ {L₁ L₂ L₃}
  → L₁ is-equally-expressive-as L₂
  → L₂ is-equally-expressive-as L₃
    ------------------------------
  → L₁ is-equally-expressive-as L₃
trans-variant-equivalence (L₁≻L₂ , L₂≻L₁) (L₂≻L₃ , L₃≻L₂) =
    trans-expressiveness L₁≻L₂ L₂≻L₃
  , trans-expressiveness L₃≻L₂ L₂≻L₁

ve-IsEquivalence : IsEquivalence _is-equally-expressive-as_
ve-IsEquivalence = record
  { refl  = refl-expressiveness , refl-expressiveness
  ; sym   = sym-variant-equivalence
  ; trans = trans-variant-equivalence
  }
```

