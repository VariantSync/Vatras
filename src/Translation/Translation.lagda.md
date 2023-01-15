# Definitions for Translation of Variability Languages

## Todo

- In a translation `conf` and `fnoc` might depend on the initial expression `e₁` in `L₁` to know features names and annotation structure to know how to properly translate. This happens when we translate from n-ary to binary choice calculus. I suppose that is reasonable.
- Can we make the definitions less clunky? For example by turning semantics into implicit parameters more frequently?
- Redefine the relations within a single language as a specialication of the relations for two languages (by comparing a language with itself)? I guess we could just leave as is because it is more didactic and enables simplifications (especially for semantic equivalence). ⇒ We could do so but it is more didactic this way. We could provide proof that they are equivalent when applied to the same single language.
- We are still missing the the annotation language over which we did not yet abstract.
- Are these definitions in line with OC for which we have an additional well-formedness constraint?
-- Is one size in the parameters enough? For CC we actually need two sizes, one constraining the tree depth and one constraining its width. This is necessary because when translating from CC to BCC, width of choices becomes depth.

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.Translation where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Size using (Size)

open import Data.Product using (_,_; ∃-syntax; _×_)
open import Existence    using (_,_; ∃-Size; ∃-syntax-with-type)

open import SemanticDomains using (Variant)
open import Extensionality  using (_embeds-via_)
```

## Definitions

We model variability languages as embedded domain specific languages.
Each language is parameterized in its object language.
```agda
Domain : Set₁ -- Object Language
Domain = Set

VarLang : Set₁
VarLang = Size → Domain → Set
```

We also model configurations as types but they do not have parameters.
```agda
ConfLang : Set₁
ConfLang = Set
```

The semantics of a language `VarLang` and its corresponding configuration language `ConfLang` is a function that configures a given expression to a variant:
```agda
Semantics : VarLang → ConfLang → Set₁
Semantics L C = ∀ {i : Size} {A : Domain} → L i A → C → Variant A
```

### Semantic equivalencies within a single language

We consider three kinds of semantic relations between two expressions `a` and `b` in the same language:
- Subset `a ⊆ b` **iff** `a` describes a subset of the variants described by `b`.
- Variant equivalence `a ≚ b` **iff** `a` and `b` describe the same set of variants (i.e., `a ⊆ b` and `b ⊆ a`)
- Semantic equivalence `a ≈ b` **iff** `a` and `b` are variant equivalent and same configurations yield same variants.

We start with semantic equivalence because it is the easierst to define.
Any two expressions `a` and `b` in a variability language `L` are equivalent if their semantics `⟦_⟧` are equivalent:
```agda
_,_⊢_≈_ : ∀ {i j : Size} {C : ConfLang} {A : Domain} → (L : VarLang) → Semantics L C → (a : L i A) → (b : L j A) → Set
L , ⟦_⟧ ⊢ a ≈ b = ⟦ a ⟧ ≡ ⟦ b ⟧
infix 5 _,_⊢_≈_
```

Semantic equivalence `≈` inherits all properties from structural equality `≡` because it is just an alias. In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence (e.g., as stated in the choice calculus TOSEM paper).

Obviously, syntactic equality (or rather structural equality) implies semantic equality:
```agda
≡→≈ : ∀ {i : Size} {L : VarLang} {C : ConfLang} {A : Domain} {a b : L i A}
  → ∀ (sem : Semantics L C)
  → a ≡ b
    ----------------
  → L , sem ⊢ a ≈ b
≡→≈ sem eq rewrite eq = refl
```

For most transformations, we are interested in a weaker form of semantic equivalence: Variant-Preserving Equivalence. Each variant that can be derived from the first expression, can also be derived from the second expression and vice versa. We thus first describe the variant-subset relation `⊆` and then define variant-equality as a bi-directional subset.
```agda
_,_⊢_⊆_ : ∀ {i j : Size} {C : ConfLang} {A : Domain}
  → (L : VarLang)
  → (⟦_⟧ : Semantics L C)
  → (e₁ : L i A)
  → (e₂ : L j A)
  → Set
_,_⊢_⊆_ {_} {_} {C} {A} _ ⟦_⟧ e₁ e₂ = ∀ (c₁ : C) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
infix 5 _,_⊢_⊆_
```

Variant subset is not symmetric, but reflexive and transitive:
```agda

-- _⊆_within_ is not symmetric.
-- _⊆_within_ is not antisymmetric because two syntactically different expression can describe the same set of variants. For example, in choice calculus `D ⟨ e , e ⟩` and `e` are different but describe the same set of variants.
-- _⊆_within_ is antisymmentric in the sense that the described set of variants is equal though which is formalized as _≚_within_ below.

⊆-refl :
  ∀ {i : Size}
    {L : VarLang} {C : ConfLang} {A : Domain}
    {e : L i A}
    {s : Semantics L C}
    --------------
  → L , s ⊢ e ⊆ e
⊆-refl c = c , refl

⊆-trans :
  ∀ {i j k : Size}
    {L : VarLang} {C : ConfLang} {A : Domain}
    {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
    {s : Semantics L C}
  → _,_⊢_⊆_ {i = i} {j = j} L s e₁ e₂
  → _,_⊢_⊆_ {i = j} {j = k} L s e₂ e₃
    ---------------------------------
  → _,_⊢_⊆_ {i = i} {j = k} L s e₁ e₃
⊆-trans x y c₁ =
  -- this somehow resembles the implementation of bind >>= of state monad
  let (c₂ , eq₁₂) = x c₁
      (c₃ , eq₂₃) = y c₂
  in c₃ , Eq.trans eq₁₂ eq₂₃
```

Variant-preserving equality:
```agda
_,_⊢_≚_ : ∀ {i j : Size} {C : ConfLang} {A : Domain}
  → (L : VarLang)
  → (⟦_⟧ : Semantics L C)
  → (e₁ : L i A)
  → (e₂ : L j A)
  → Set
_,_⊢_≚_ {i} {j} {C} {A} L s e₁ e₂ =
    (_,_⊢_⊆_ {i} {j} {C} {A} L s e₁ e₂)
  × (_,_⊢_⊆_ {j} {i} {C} {A} L s e₂ e₁)
infix 5 _,_⊢_≚_
```


Variant-preserving equality is an equivalence relation:
```agda
≚-refl :
  ∀ {i : Size}
    {L : VarLang} {C : ConfLang} {A : Domain}
    {e : L i A}
    {s : Semantics L C}
    --------------
  → L , s ⊢ e ≚ e
≚-refl {i} {L} {C} {A} {e} {s} =
    ⊆-refl {i} {L} {C} {A} {e} {s}
  , ⊆-refl {i} {L} {C} {A} {e} {s}

≚-sym :
  ∀ {i j : Size}
    {L : VarLang} {C : ConfLang} {A : Domain}
    {e₁ : L i A} {e₂ : L j A}
    {s : Semantics L C}
  → _,_⊢_≚_ {i = i} {j = j} L s e₁ e₂
    ---------------------------------
  → _,_⊢_≚_ {i = j} {j = i} L s e₂ e₁
≚-sym (e₁⊆e₂ , e₂⊆e₁) = e₂⊆e₁ , e₁⊆e₂

≚-trans :
  ∀ {i j k : Size}
    {L : VarLang} {C : ConfLang} {A : Domain}
    {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
    {s : Semantics L C}
  → _,_⊢_≚_ {i = i} {j = j} L s e₁ e₂
  → _,_⊢_≚_ {i = j} {j = k} L s e₂ e₃
    ---------------------------------
  → _,_⊢_≚_ {i = i} {j = k} L s e₁ e₃
≚-trans {i} {j} {k} {L} {C} {A} {e₁} {e₂} {e₃} {s} (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂) =
    ⊆-trans {i} {j} {k} {L} {C} {A} {e₁} {e₂} {e₃} {s} e₁⊆e₂ e₂⊆e₃
  , ⊆-trans {k} {j} {i} {L} {C} {A} {e₃} {e₂} {e₁} {s} e₃⊆e₂ e₂⊆e₁
```

Semantic equality implies variant equality:
```agda
≈→⊆ :
  ∀ {i j : Size}
    {L : VarLang} {C : ConfLang} {s : Semantics L C}
    {A : Domain}
    {a : L i A} {b : L j A}
  → L , s ⊢ a ≈ b
    -------------
  → L , s ⊢ a ⊆ b
-- From a≈b, we know that ⟦ a ⟧ ≡ ⟦ b ⟧. To prove subset, we have to show that both sides produce the same variant for a given configuration. We do so by applying the configuration to both sides of the equation of a≈b.
≈→⊆ a≈b config = config , Eq.cong (λ ⟦x⟧ → ⟦x⟧ config) a≈b

≈→≚ : ∀ {i j : Size} {L : VarLang} {C : ConfLang} {s : Semantics L C} {A : Domain} {a : L i A} {b : L j A}
  → L , s ⊢ a ≈ b
    -------------
  → L , s ⊢ a ≚ b
≈→≚ {i} {j} {L} {C} {s} {A} {a} {b} a≈b =
    ≈→⊆ {i} {j} {L} {C} {s} {A} {a} {b} a≈b
  , ≈→⊆ {j} {i} {L} {C} {s} {A} {b} {a} (Eq.sym a≈b)
```

## Comparing Languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.
Finally, we formalize translations between languages and show that creating translations allows us to conclude certain relations between languages.

### Definitions of equivalencies across languages

First we generalize `_⊆_within_` and `_≚_within_` from single languages to two different languages.
This step is straighforward as it just requires us to introduce additional parameters for the second language and reformulating the right-hand side of relations to refer to the second language.
The main insight here is that we can compare expressions across languages because they share the same semantic domain: variants.
```agda
_,_and_,_⊢_⊆_ : ∀ {i j : Size} {C₁ C₂ : ConfLang} {A : Domain}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → Set
_,_and_,_⊢_⊆_ {_} {_} {C₁} {_} {_} _  ⟦_⟧₁ _ ⟦_⟧₂ e₁ e₂ =
  ∀ (c₁ : C₁) → ∃[ c₂ ] (⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₂ ⟧₂ c₂)

_,_and_,_⊢_≚_ : ∀ {i j : Size} {C₁ C₂ : ConfLang} {A : Domain}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → Set
_,_and_,_⊢_≚_ {i} {j} {C₁} {C₂} {A} L₁ s₁ L₂ s₂ e₁ e₂ =
    (_,_and_,_⊢_⊆_ {i} {j} {C₁} {C₂} {A} L₁ s₁ L₂ s₂ e₁ e₂)
  × (_,_and_,_⊢_⊆_ {j} {i} {C₂} {C₁} {A} L₂ s₂ L₁ s₁ e₂ e₁)
```

### Comparing languages as a whole

We say that a language `L₂` is as expressive as another language `L₁` **iff** for any expression `e₁` in `L₁`, there exists an expression `e₂` in `L₂` that describes the same set of variants. This means that there exists a translation from `L₁` to `L₂`, and thus `L₂` can model `L₁`:
```agda
_,_is-as-expressive-as_,_ : {C₁ C₂ : ConfLang}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → Set₁
L₁ , S₁ is-as-expressive-as L₂ , S₂ =
  ∀ {j : Size} {A : Domain} (e₂ : L₂ j A) →
    ∃-Size[ i ]
      (∃[ e₁ ∈ (L₁ i A)]
        (L₂ , S₂ and L₁ , S₁ ⊢ e₂ ≚ e₁))
```

A language `L₁` is variant equivalent to another language `L₂` **iff** they are equally expressive. This means that we can translate between both languages.
```agda
_,_is-variant-equivalent-to_,_ : {C₁ C₂ : ConfLang}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → Set₁
L₁ , S₁ is-variant-equivalent-to L₂ , S₂ =
    (L₁ , S₁ is-as-expressive-as L₂ , S₂)
  × (L₂ , S₂ is-as-expressive-as L₁ , S₁)
```

### Translations

A translation translates (1) a variability language `L₁` to another variability language `L₂`, as well as (2) the corresponding configuration language `C₁` to `C₂`.
The first translation is modelled as the `lang` field below while the translation of configurations is modelled by the `conf` and `fnoc` (inverse of _conf_).
A translation also has to translate configurations backwards from `C₂` to `C₁`
While this asymmetry (compared to the translation of the variability language) seems weird, the backwards translation of configurations is necessary to compare the sets of described variants of the target language `L₂` with the ones in the source language `L₁`.
For convenience, a translation also carries the semantics of the language it intends to preserve. This might not really be necessary but it purifies the below definitions.
```agda
record Translation (L₁ L₂ : VarLang) (C₁ C₂ : ConfLang) : Set₁ where
  field
    sem₁ : Semantics L₁ C₁
    sem₂ : Semantics L₂ C₂

    size : Size → Size
    lang : ∀ {i : Size} {D : Domain} → L₁ i D → L₂ (size i) D
    conf : C₁ → C₂
    fnoc : C₂ → C₁ -- We need this to quantify over the set of variants described by the translated expression.
open Translation public
```

We now reformulate our relations to compare expressions between languages to translations.
An expression `e₁` describes a subset of the variants of its translated expression `lang translation e₁` if we can also translate the configuration to produce the same variant.
```agda
_⊆-via_ : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain}
  → (e₁ : L₁ i A)
  → Translation L₁ L₂ C₁ C₂
  → Set
_⊆-via_ {_} {_} {_} {C₁} {_} {_} e₁ translation =
  let ⟦_⟧₁ = sem₁ translation
      ⟦_⟧₂ = sem₂ translation
  in
      ∀ (c₁ : C₁) → (⟦ e₁ ⟧₁ c₁ ≡ ⟦ lang translation e₁ ⟧₂ (conf translation c₁))
```

From our reformulation for translations, we can indeed conclude that an expression describes a subset of the variants of its translated expression.
```agda
⊆-via→⊆-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → _⊆-via_ {i} {L₁} {L₂} {_} {_} {_} e₁ t
    ---------------------------------------------------------------------------
  → _,_and_,_⊢_⊆_ {i = i} {j = size t i} L₁ (sem₁ t) L₂ (sem₂ t) e₁ (lang t e₁)
⊆-via→⊆-within {i} t ⊆-via = λ c₁ → conf t c₁ , ⊆-via c₁
```

Analogously, we proceed for the inverse direction.
We cannot reuse our above definitions as we did for `_⊆-_within_and_` because we do not quantify over the second expression anymore as it is derived from applying the translation to the expression `e₁` in the source language `L₁ A`.
To check if a variant described by translated expression `lang translation e₁` is also described by the original expression `e₁`, we have to inspect whether any possible configuration of the translated expression can also be made to `e₁`.
That is the reason why we require translations to also provide backwards translations for configurations: We are not directly dealing with sets of variants but with the semantics as a function describing this set indirectly via its configuration parameter.
```agda
_⊇-via_ : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain}
  → (e₁ : L₁ i A)
  → Translation L₁ L₂ C₁ C₂
  → Set
_⊇-via_ {_} {_} {_} {_} {C₂} {_} e₁ translation =
  let ⟦_⟧₁ = sem₁ translation
      ⟦_⟧₂ = sem₂ translation
  in
    ∀ (c₂ : C₂) → (⟦ e₁ ⟧₁ (fnoc translation c₂) ≡ ⟦ lang translation e₁ ⟧₂ c₂)

-- Proof that our definition of translation is sufficient to conclude variant-subset of an expression and its translation.
⊇-via→⊆-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → e₁ ⊇-via t
    ----------------------------------------------------
  → _,_and_,_⊢_⊆_ L₂ (sem₂ t) L₁ (sem₁ t) (lang t e₁) e₁
⊇-via→⊆-within t ⊇-via = λ c₂ → fnoc t c₂ , Eq.sym (⊇-via c₂)
```

As earlier, we can compose the above definitions to say that an expression `e₁` describes the same set of variants as its translated expression.
```agda
_≚-via_ : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain}
  → (e₁ : L₁ i A)
  → Translation L₁ L₂ C₁ C₂
  → Set
_≚-via_ {_} {_} {_} {C₁} {_} {_} e₁ t =
    e₁ ⊆-via t
  × e₁ ⊇-via t

≚-via→≚-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → e₁ ≚-via t
    --------------------------------------------------
  → L₁ , (sem₁ t) and L₂ , (sem₂ t) ⊢ e₁ ≚ (lang t e₁)
≚-via→≚-within t (⊆-via , ⊇-via) =
    ⊆-via→⊆-within t ⊆-via
  , ⊇-via→⊆-within t ⊇-via
```

Finally, we can establish whether a translation is variant- or semantics-preserving.
A translation is variability-preserving if it translates every expression ot a variant-equivalent expression.
This is one of the major theorems we ought to show for translation between variability languages.
```agda
_is-variant-preserving : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} → Translation L₁ L₂ C₁ C₂ → Set₁
_is-variant-preserving {L₁} {_} {_} {_} t = ∀ {i : Size} {A : Domain} (e₁ : L₁ i A) → e₁ ≚-via t
```

A translation is semantics preserving iff its semantics preserving and the same configuration yields the same variants.
We identify a configuration to be the same if it can be uniquely translated back (i.e., if `conf` is an embedding into `C₂` via its inverse `fnoc`).
We do not require the inverse direction (`fnoc` being an embedding of configurations from `C₂` into `C₁`) because `C₂` could be larger than `C₁` (when interpreted as a set).
For example, the set of features in `C₂` could be bigger (e.g., when going from core choice calculus to binary choice calculus) but all information can be derived by `conf` from our initial configuration `c₁`.
```agda
_is-semantics-preserving : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} → Translation L₁ L₂ C₁ C₂ → Set₁
_is-semantics-preserving {_} {_} {C₁} {_} t =
    t is-variant-preserving
  × (conf t) embeds-via (fnoc t)
```

We can conclude that a language is as expressive as another language if there exists a variant preserving translation.
This is our major theorem that allows us to prove relations about languages from writing translations.
```agda
translation-proves-variant-preservation : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang}
  → (t : Translation L₁ L₂ C₁ C₂)
  → t is-variant-preserving
    -----------------------------------------------
  → L₂ , (sem₂ t) is-as-expressive-as L₁ , (sem₁ t)
translation-proves-variant-preservation trans preservation {i} {_} e₁ =
    size trans i
  , lang trans e₁
  , ≚-via→≚-within trans (preservation e₁)
```
