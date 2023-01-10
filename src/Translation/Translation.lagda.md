# Definitions for Translation of Variability Languages

## Module

```agda
module Translation.Translation where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import SemanticDomains
```

## Definitions

We model variability languages as embedded domain specific languages.
Each language is parameterized in its object language.
```agda
VarLang : Set₁
VarLang = Set → Set
```

We also model configurations as types but they do not have parameters.
```agda
ConfLang : Set₁
ConfLang = Set
```

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → ConfLang → Set₁
Semantics L C = ∀ {A : Set} → L A → C → Variant A
```

### Semantic equivalencies within a single language

We consider three kinds of semantic relations between two expressions `a` and `b` in the same language:
- Subset `a ⊆ b` **iff** `a` describes a subset of the variants described by `b`.
- Variant equivalence `a ≚ b` **iff** `a` and `b` describe the same set of variants (i.e., `a ⊆ b` and `b ⊆ a`)
- Semantic equivalence `a ≈ b` **iff** `a` and `b` are variant equivalent and same configurations yield same variants.

We start with semantic equivalence because it is the easierst to define.
Any two expressions are equivalent if their semantics are equivalent:
```agda
_≈_within_ : {L : VarLang} {C : ConfLang} {A : Set} → (a b : L A) → Semantics L C → Set
a ≈ b within ⟦_⟧ = ⟦ a ⟧ ≡ ⟦ b ⟧
infix 5 _≈_within_
```

Obviously, syntactic equality (or rather structural equality) implies semantic equality:
```agda
≡→≈ : ∀ {L : VarLang} {C : ConfLang} {A : Set} {a b : L A}
  → ∀ (sem : Semantics L C)
  → a ≡ b
    ----------------
  → a ≈ b within sem
≡→≈ sem eq rewrite eq = refl
```

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence. Each variant that can be derived from the first expression, can also be derived from the second expression and vice versa. We thus first describe the variant-subset relation `⊆` and then define variant-equality as a bi-directional subset.
```agda
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)

_⊆_within_ : ∀ {L : VarLang} {C : ConfLang} {A : Set}
  → (e₁ e₂ : L A)
  → (⟦_⟧ : Semantics L C)
  → Set
_⊆_within_ {L} {C} {A} e₁ e₂ ⟦_⟧ = ∀ (c₁ : C) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
infix 5 _⊆_within_

-- Alternative definition via `data`
--data _⊆_ {L : VarLang} {C : ConfLang} {⟦_⟧ : Semantics L C} {A : Set} (e₁ e₂ : L A) : Set where
--  yes : ∀ (c₁ : C) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂) → e₁ ⊆ e₂
```

Variant subset is not symmetric, but reflexive and transitive:
```agda

-- _⊆_within_ is not symmetric.
-- _⊆_within_ is not antisymmetric because two syntactically different expression can describe the same set of variants. For example, in choice calculus `D ⟨ e , e ⟩` and `e` are different but describe the same set of variants.

⊆-refl : ∀ {L : VarLang} {C : ConfLang} {A : Set} {e : L A} {s : Semantics L C}
    --------------
  → e ⊆ e within s
⊆-refl c = c , refl

⊆-trans : ∀ {L : VarLang} {C : ConfLang} {A : Set} {e₁ e₂ e₃ : L A} {s : Semantics L C}
  → e₁ ⊆ e₂ within s
  → e₂ ⊆ e₃ within s
    ----------------
  → e₁ ⊆ e₃ within s
⊆-trans x y c₁ =
  -- this somehow resembles the implementation of bind >>= of state monad
  let (c₂ , eq₁₂) = x c₁
      (c₃ , eq₂₃) = y c₂
  in c₃ , Eq.trans eq₁₂ eq₂₃
```

Variant-preserving equality:
```agda
_≚_within_ : ∀ {L : VarLang} {C : ConfLang} {A : Set}
  → (e₁ e₂ : L A)
  → (⟦_⟧ : Semantics L C)
  → Set
e₁ ≚ e₂ within s = (e₁ ⊆ e₂ within s) × (e₂ ⊆ e₁ within s)
```

Variant-preserving equality is an equivalence relation:
```agda
≚-refl : ∀ {L : VarLang} {C : ConfLang} {A : Set} {e : L A} {s : Semantics L C}
    --------------
  → e ≚ e within s
≚-refl {L} {C} {A} {e} {s} =
    ⊆-refl {L} {C} {A} {e} {s}
  , ⊆-refl {L} {C} {A} {e} {s}

≚-sym : ∀ {L : VarLang} {C : ConfLang} {A : Set} {e₁ e₂ : L A} {s : Semantics L C}
  → e₁ ≚ e₂ within s
    ----------------
  → e₂ ≚ e₁ within s
≚-sym (e₁⊆e₂ , e₂⊆e₁) = e₂⊆e₁ , e₁⊆e₂

≚-trans : ∀ {L : VarLang} {C : ConfLang} {A : Set} {e₁ e₂ e₃ : L A} {s : Semantics L C}
  → e₁ ≚ e₂ within s
  → e₂ ≚ e₃ within s
    ----------------
  → e₁ ≚ e₃ within s
≚-trans {L} {C} {A} {e₁} {e₂} {e₃} {s} (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂) =
    ⊆-trans {L} {C} {A} {e₁} {e₂} {e₃} {s} e₁⊆e₂ e₂⊆e₃
  , ⊆-trans {L} {C} {A} {e₃} {e₂} {e₁} {s} e₃⊆e₂ e₂⊆e₁
```

## Comparing Languages

### Definitions of equivalencies across languages

### Comparing languages as a whole

Expressiveness:
```agda
--_is-as-expressive-as_ : (L₁ L₂ : VarLang) → Set
--L₁ is-as-expressive-as L₂ = ∀ (e₁ : L₁) → ∃[e₂ : L₂] (e₁ ≚ e₂ within)
```

### Translations
```agda
record Translation (L₁ C₁ L₂ C₂ : Set) : Set where
  field
    of-lang   : L₁ → L₂
    of-config : C₁ → C₂

record SemanticPreserving (L₁ C₁ L₂ C₂ : Set) : Set where
--  field
    --translation : Translation L₁ C
```

