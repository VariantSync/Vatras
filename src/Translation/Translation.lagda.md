# Definitions for Translation of Variability Languages

## Todo

- In a translation `conf` and `fnoc` might depend on the initial expression `e₁` in `L₁` to know features names and annotation structure to know how to properly translate. This happens when we translate from n-ary to binary choice calculus. I suppose that is reasonable.
- Can we make the definitions less clunky? For example by turning semantics into implicit parameters more frequently?
- Redefine the relations within a single language as a specialication of the relations for two languages (by comparing a language with itself)? I guess we could just leave as is because it is more didactic and enables simplifications (especially for semantic equivalence). ⇒ We could do so but it is more didactic this way. We could provide proof that they are equivalent when applied to the same single language.
- We are still missing the the annotation language over which we did not yet abstract.
- Are these definitions in line with OC for which we have an additional well-formedness constraint?
- Is one size in the parameters enough? For CC we actually need two sizes, one constraining the tree depth and one constraining its width. This is necessary because when translating from CC to BCC, width of choices becomes depth.
- Syntactic equivalence between languages: binary choice calculus expressions are actually also core choice calculus expressions because every binary choice is an n-ary choice. Every ADD is also a binary choice calculus expression. How can we formalize this? Our current relations allow us to say "only" that the CCC is as expressive as CCC and BCC is as expressive as ADDs but without information that these languages actually _embed_ into each other. So we might want to formalize a more concrete kind of translation: an embedding (i.e., a one way isomorphism). We could then prove that a language can be trivially translated to the other language and back without any changes. Even an embedding could allow syntactically manipulations though as long as they can be uniquely reversed. Is there any way to exclude such transformations? Maybe we want to allow them? Checking out the extended embedding translations might be a first useful step though.

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
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

open import Data.Product   using (_,_; ∃-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size; proj₁; proj₂; ∃-syntax-with-type)

open import SemanticDomain using (Variant)
open import Axioms.Extensionality using (_embeds-via_)
```

## Definitions

We model variability languages as embedded domain specific languages. That is, each variability language is described by a type which in turn is described by the kind `VarLang`. (`Set` denotes the set of all types and `Set₁` denotes the set of all kinds, i.e., the set of all sets of types).
Each language is parameterized in its domain (called _object language_ in choice calculus), such as text, source code, files, whatever.
We model domains, also as types, such as `String`, `ℕ`, or some AST of a programming language.
Each variability language `VarLang` is also parameterized in a size which is irrelevant for studying variation but we need it to ensure that our proofs terminate.
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

We start with semantic equivalence because it is the easiest to define.
Any two expressions `a` and `b` in a variability language `L` are equivalent if their semantics `⟦_⟧` are equivalent:
```agda
_,_⊢_≈_ : ∀ {i j : Size} {C : ConfLang} {A : Domain}
  → (L : VarLang)
  → Semantics L C
  → L i A
  → L j A
  → Set
L , ⟦_⟧ ⊢ e₁ ≈ e₂ = ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
infix 5 _,_⊢_≈_
```
A proposition `L , ⟦_⟧ ⊢ e₁ ≈ e₂` reads as, in a language `L` with semantics `⟦_⟧` the expressions `e₁` and `e₂` are semantically equivalent, i.e., `⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧`.

Semantic equivalence `≈` inherits all properties from structural equality `≡` because it is just an alias. In particular, these properties include reflexivity (by definition), symmetry, transitivity, and congruence (e.g., as stated in the choice calculus TOSEM paper).

Obviously, syntactic equality (or rather structural equality) implies semantic equality, independent of the semantics:
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
  → Semantics L C
  → L i A
  → L j A
  → Set
_,_⊢_⊆_ {_} {_} {C} {_} _ ⟦_⟧ e₁ e₂ = ∀ (c₁ : C) → ∃[ c₂ ] (⟦ e₁ ⟧ c₁ ≡ ⟦ e₂ ⟧ c₂)
infix 5 _,_⊢_⊆_
```
A proposition `L , ⟦_⟧ ⊢ e₁ ⊆ e₂` reads as, in a language `L` with semantics `⟦_⟧` the expression `e₁` describes a subset of the variants described by `e₂`.

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
  → Semantics L C
  → L i A
  → L j A
  → Set
_,_⊢_≚_      {i}     {j}    {_} {_} L s e₁ e₂ =
    (_,_⊢_⊆_ {i = i} {j = j}        L s e₁ e₂)
  × (_,_⊢_⊆_ {i = j} {j = i}        L s e₂ e₁)
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
≚-trans     {i} {j} {k} {L} {C} {A} {e₁} {e₂} {e₃} {s} (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂) =
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
≈→⊆ a≈b config = config , Eq.cong (λ s → s config) a≈b

≈→≚ : ∀ {i j : Size} {L : VarLang} {C : ConfLang} {s : Semantics L C} {A : Domain} {a : L i A} {b : L j A}
  → L , s ⊢ a ≈ b
    -------------
  → L , s ⊢ a ≚ b
≈→≚     {i} {j} {L} {C} {s} {A} {a} {b} a≈b =
    ≈→⊆ {i} {j} {L} {C} {s} {A} {a} {b} a≈b
  , ≈→⊆ {j} {i} {L} {C} {s} {A} {b} {a} (Eq.sym a≈b)
```

## Comparing Languages

To compare languages, we first define relations for comparing expressions between different languages.
Then we leverage these relations to model relations between whole languages.
Finally, we formalize translations between languages and show that creating translations allows us to conclude certain relations between languages.

### Definitions of equivalencies across languages

First we generalize `_,_⊢_⊆_` and `_,_⊢_≚_` from single languages to two different languages.
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
_,_and_,_⊢_≚_      {i} {j} {C₁} {C₂} {A} L₁ s₁ L₂ s₂ e₁ e₂ =
    (_,_and_,_⊢_⊆_ {i} {j} {C₁} {C₂} {A} L₁ s₁ L₂ s₂ e₁ e₂)
  × (_,_and_,_⊢_⊆_ {j} {i} {C₂} {C₁} {A} L₂ s₂ L₁ s₁ e₂ e₁)
```

### Comparing languages as a whole

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
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

A language `L₁` is variant equivalent to another language `L₂` **iff** they are equally expressive. This means that we can translate between both languages. (We cannot prove the existence of a translation though because we cannot find a translation automatically. We use the inverse route, concluding propositions about languages from building translations later.)
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
Moreover, a translation also has to translate the size constraints over languages so that we can express that a translated expression does not become infinitely large.
```agda
record TranslationResult (A : Domain) (L₂ : VarLang) (C₁ C₂ : ConfLang) : Set where
  field
    size : Size
    expr : L₂ size A
    conf : C₁ → C₂
    fnoc : C₂ → C₁
open TranslationResult public

record Translation (L₁ L₂ : VarLang) (C₁ C₂ : ConfLang) : Set₁ where
  field
    sem₁ : Semantics L₁ C₁
    sem₂ : Semantics L₂ C₂
    translate : ∀ {i : Size} {D : Domain} → L₁ i D → TranslationResult D L₂ C₁ C₂
open Translation public

getSize : ∀ {i : Size} {D : Domain} {L : VarLang} → L i D → Size
getSize {i = i} _ = i
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
      ∀ (c₁ : C₁) → (⟦ e₁ ⟧₁ c₁ ≡ ⟦ expr (translate translation e₁) ⟧₂ (conf (translate translation e₁) c₁))
```

From our reformulation for translations, we can indeed conclude that an expression describes a subset of the variants of its translated expression.
```agda
⊆-via→⊆-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → _⊆-via_ {_} {L₁} {L₂} {_} {_} {_} e₁ t
    --------------------------------------------
  → L₁ , sem₁ t and L₂ , sem₂ t ⊢ e₁ ⊆ expr (translate t e₁)
⊆-via→⊆-within {e₁ = e₁} t ⊆-via = λ c₁ → conf (translate t e₁) c₁ , ⊆-via c₁
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
    ∀ (c₂ : C₂) → (⟦ e₁ ⟧₁ (fnoc (translate translation e₁) c₂) ≡ ⟦ expr (translate translation e₁) ⟧₂ c₂)

-- Proof that our definition of translation is sufficient to conclude variant-subset of an expression and its translation.
⊇-via→⊆-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → e₁ ⊇-via t
    --------------------------------------------
  → L₂ , sem₂ t and L₁ , sem₁ t ⊢ expr (translate t e₁) ⊆ e₁
⊇-via→⊆-within {e₁ = e₁} t ⊇-via = λ c₂ → fnoc (translate t e₁) c₂ , Eq.sym (⊇-via c₂)
```

As earlier, we can compose the above definitions to say that an expression `e₁` describes the same set of variants as its translated expression.
```agda
_≚-via_ : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain}
  → (e₁ : L₁ i A)
  → Translation L₁ L₂ C₁ C₂
  → Set
e₁ ≚-via t = e₁ ⊆-via t × e₁ ⊇-via t

≚-via→≚-within : ∀ {i : Size} {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {A : Domain} → {e₁ : L₁ i A}
  → (t : Translation L₁ L₂ C₁ C₂)
  → e₁ ≚-via t
    --------------------------------------------
  → L₁ , sem₁ t and L₂ , sem₂ t ⊢ e₁ ≚ expr (translate t e₁)
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
_is-semantics-preserving {L₁ = L₁} t =
    t is-variant-preserving
  × (∀ {i : Size} {A : Domain} (e₁ : L₁ i A) → (conf (translate t e₁)) embeds-via (fnoc (translate t e₁)))
```

We can conclude that a language is as expressive as another language if there exists a variant preserving translation.
This is our major theorem that allows us to prove relations about languages from writing translations.
```agda
translation-proves-variant-preservation : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang}
  → (t : Translation L₁ L₂ C₁ C₂)
  → t is-variant-preserving
    -------------------------------------------
  → L₂ , sem₂ t is-as-expressive-as L₁ , sem₁ t
translation-proves-variant-preservation trans preservation e₁ =
  let r = translate trans e₁ in
    size r
  , expr r
  , ≚-via→≚-within trans (preservation e₁)
```

### Helper Functions and Theorems

```agda
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
open import Size using (Size<_; ↑_; _⊔ˢ_)
open import Util.SizeJuggle

{-
Given a list of individually sized expressions, we find the maximum size and cast every expression to that maximum size. In case the list is empty, the given default value is returned.
-}
unify-sizes : ∀ {A : Domain} → (L : VarLang) → Size → List (∃-Size[ i ] (L i A)) → ∃-Size[ max ] (List (L max A))
unify-sizes _ ε [] = ε , []
unify-sizes L ε ((i , e) ∷ xs) =
  let (max-tail , tail) = unify-sizes L ε xs
   in i ⊔ˢ max-tail , e ∷ tail -- Why is there a warning highlight without a message here?

{-
Same as max-size⁺ but for non-empty list.
We can thus be sure that a maximum size exist and do not need a default value.
-}
unify-sizes⁺ : ∀ {A : Domain} → (L : VarLang) → List⁺ (∃-Size[ i ] (L i A)) → ∃-Size[ max ] (List (L max A))
unify-sizes⁺ L list@((i , _) ∷ _) = unify-sizes L i (toList list)

{-
Most languages feature Artifacts as arbitrary elements of the domain language.
The constructor usually takes an element of the domain and a list of child expressions.
-}
Artifactˡ : VarLang → Set₁
Artifactˡ L = ∀ {i : Size} {j : Size< i} {A : Domain} → A → List (L j A) → L i A

{-
Creates an Artifact₂ from a list of expressions of a certain size.
The size of the resulting expression is larger by 1.
-}
sequence-sized-artifact : ∀ {A : Domain}
  → {L : VarLang}
  → Artifactˡ L
  → A
  → List⁺ (∃-Size[ i ] (L i A))
    ----------------------------
  → ∃-Size[ i ] (L i A)
sequence-sized-artifact {A} {L} Artifact a cs =
  let max , es = unify-sizes⁺ L cs in
  ↑ max , Artifact {↑ max} {max} {A} a es
```


## Stronger Relations

### Strong Syntactic Equivalence

So far, we covered relations between languages on a semantic level: Can we translate languages such that the translation describes the same set of variants as the original expression.
Some languages though exhibit stronger similarities, even up to syntactic equality.
For example, all terms in binary choice calculus _are_ also terms in core choice calculus.
This subset relation is not immediate in our formalization thought because both languages are modelled as their own datatypes and thus, syntactically equal terms are still instances of two different datatypes.

So how can we say that an expression `e` in a language `L` _is_ also an expression in another language `L'` (i.e., `e ∈ L` and `e ∈ L'`)?
To immediately obtain such a property, we would have to show that `e` is an instance of both types, which is impossible in Agda. (Todo: How is this property of a type system called?) What we can do however is matching constructors: When "translating" `e ∈ L` to `e' ∈ L'`, all we do is matching one constructor the at least one other constructor. If such a matching is injective, then we have shown that `e` is indeed an expression in `L'` up to some rewriting in terms of one or more constructors. We can then further constrain such a mapping to map each constructor to exactly one other constructor.

So what we want to say is: For every expression `e ∈ L₁`, having some constructor `C₁` at the top, there exists (exactly one / a) constructor `C₂` in `L₂` such that swapping the constructor from `C₁` to `C₂` in `e` yields a semantically equivalent expression `e₂ ∈ L₂`.

How can we formalized this in Agda though? One idea is to again treat constructors as their own types. A constructor for a variability language `L` is a function that takes some parameter `P` to produce an instance of that type.
```agda
VarLangConstructor : VarLang → Set₁
VarLangConstructor L = ∀ {i : Size} {A : Domain} {P : Set} → P → L i A
```
The set of constructors described by `VarLangConstructor L` for a language `L` is larger though than the actual set of `L`'s constructors as any function producing an `L`-expression would be a `VarLangConstructor L`. The constructors we seek are the "atomic" ones. Any `c : VarLangConstructor L` either is such an atomic constructor or composes an expression by applying atomic constructors one or more times. How can we identify the atomic constructors? This sounds like a job for category theory where we want to find some terminal/initial object.

TODO: More thinking. Can we properly express this in Agda? We could also comare constructors by looking at the translations outside of Agda.

### Weak Syntactic Equivalence

One observation is that, iff any term `e ∈ L₁` is also a term in `L₂`, then we it can be translated to L₂ and back to L₁ yielding the same term `e`.
Formalizing this constraint, would not guarantee that a translated term `e₂` is really syntactically equivalent to the original term `e₁` but it would depict that `e₂` contains enough information to recover `e₁` uniquely (but `e₂` might contain more information). This is a one-way isomorphism, also know as an embedding:
```agda
record LanguageEmbedding (L₁ L₂ : VarLang) : Set₁ where
  field
    to   : ∀ {i : Size} {D : Domain} → L₁ i D → L₂ i D
    from : ∀ {i : Size} {D : Domain} → L₂ i D → L₁ i D
    from∘to : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₁ i D} {L₂ i D} to from
open LanguageEmbedding public

record LanguageIsomorphism (L₁ L₂ : VarLang) : Set₁ where
  field
    to   : ∀ {i : Size} {D : Domain} → L₁ i D → L₂ i D
    from : ∀ {i : Size} {D : Domain} → L₂ i D → L₁ i D
    from∘to : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₁ i D} {L₂ i D} to from
    to∘from : ∀ {i : Size} {D : Domain} → _embeds-via_ {L₂ i D} {L₁ i D} from to
open LanguageIsomorphism public

open Eq using (_≗_)
embedding→isomorphism : ∀ {L₁ L₂ : VarLang}
  → (1→2 : LanguageEmbedding L₁ L₂)
  → (2→1 : LanguageEmbedding L₂ L₁)
  → (∀ {i : Size} {D : Domain} → from 1→2 {i} {D} ≗   to 2→1 {i} {D})
  → (∀ {i : Size} {D : Domain} →   to 2→1 {i} {D} ≗ from 1→2 {i} {D})
    -------------------------
  → LanguageIsomorphism L₁ L₂
embedding→isomorphism 1→2 2→1 f≡t t≡f = record
  { to = to 1→2
  ; from = from 1→2
  ; from∘to = from∘to 1→2
  ; to∘from = λ e₂ → ({!!})
  }
```
Additionally, we enforce the size to be constant as the expression should not change anyway. A problem might be if the size constraint has different meanings in both langauges (e.g., depth vs. breadth). So we might want to weaken this in the future.

