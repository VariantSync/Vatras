```agda
{-# OPTIONS --sized-types #-}

module Relations.Semantic where
```

# Relations of Variability Languages

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Size using (Size)

open import Data.Product   using (_,_; ∃-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size; ∃-syntax-with-type)

open import Relation.Nullary.Negation using (¬_)

open import Definitions
```

## Semantic Relations of Expressions Within a Single Language

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
  ∀ {i : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {e : L i A}
    --------------
  → L , S ⊢ e ⊆ e
⊆-refl c = c , refl

⊆-trans :
  ∀ {i j k : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
  → _,_⊢_⊆_ {i = i} {j = j} L S e₁ e₂
  → _,_⊢_⊆_ {i = j} {j = k} L S e₂ e₃
    ---------------------------------
  → _,_⊢_⊆_ {i = i} {j = k} L S e₁ e₃
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
  ∀ {i : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {e : L i A}
    --------------
  → L , S ⊢ e ≚ e
≚-refl {i} {A} {L} {C} {e} {s} =
    ⊆-refl {i} {A} {L} {C} {e} {s}
  , ⊆-refl {i} {A} {L} {C} {e} {s}

≚-sym :
  ∀ {i j : Size} {A : Domain}
    {L : VarLang} {C : ConfLang}
    {e₁ : L i A} {e₂ : L j A}
    {S : Semantics L C}
  → _,_⊢_≚_ {i = i} {j = j} L S e₁ e₂
    ---------------------------------
  → _,_⊢_≚_ {i = j} {j = i} L S e₂ e₁
≚-sym (e₁⊆e₂ , e₂⊆e₁) = e₂⊆e₁ , e₁⊆e₂

≚-trans :
  ∀ {i j k : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {s : Semantics L C}
    {e₁ : L i A} {e₂ : L j A} {e₃ : L k A}
  → _,_⊢_≚_ {i = i} {j = j} L s e₁ e₂
  → _,_⊢_≚_ {i = j} {j = k} L s e₂ e₃
    ---------------------------------
  → _,_⊢_≚_ {i = i} {j = k} L s e₁ e₃
≚-trans     {i} {j} {k} {A} {L} {C} {S} {e₁} {e₂} {e₃} (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂) =
    ⊆-trans {i} {j} {k} {A} {L} {C} {S} {e₁} {e₂} {e₃} e₁⊆e₂ e₂⊆e₃
  , ⊆-trans {k} {j} {i} {A} {L} {C} {S} {e₃} {e₂} {e₁} e₃⊆e₂ e₂⊆e₁
```

Semantic equality implies variant equality:
```agda
≈→⊆ :
  ∀ {i j : Size} {A : Domain}
    {L : VarLang} {C : ConfLang} {S : Semantics L C}
    {a : L i A} {b : L j A}
  → L , S ⊢ a ≈ b
    -------------
  → L , S ⊢ a ⊆ b
-- From a≈b, we know that ⟦ a ⟧ ≡ ⟦ b ⟧. To prove subset, we have to show that both sides produce the same variant for a given configuration. We do so by applying the configuration to both sides of the equation of a≈b.
≈→⊆ a≈b config = config , Eq.cong (λ s → s config) a≈b

≈→≚ :
  ∀ {i j : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {a : L i A} {b : L j A}
  → L , S ⊢ a ≈ b
    -------------
  → L , S ⊢ a ≚ b
≈→≚     {i} {j} {A} {L} {C} {S} {a} {b} a≈b =
    ≈→⊆ {i} {j} {A} {L} {C} {S} {a} {b} a≈b
  , ≈→⊆ {j} {i} {A} {L} {C} {S} {b} {a} (Eq.sym a≈b)
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

In the following the prove the same properties as for the relations within a single language. The proofs are identical:
```agda
⊆-refl' :
  ∀ {i : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {e : L i A}
    -----------------------
  → L , S and L , S ⊢ e ⊆ e
⊆-refl' c = c , refl

⊆-trans' :
  ∀ {i j k : Size} {A : Domain}
    {L₁ L₂ L₃ : VarLang}
    {C₁ C₂ C₃ : ConfLang}
    {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {S₃ : Semantics L₃ C₃}
    {e₁ : L₁ i A} {e₂ : L₂ j A} {e₃ : L₃ k A}
  → _,_and_,_⊢_⊆_ {i = i} {j = j} L₁ S₁ L₂ S₂ e₁ e₂
  → _,_and_,_⊢_⊆_ {i = j} {j = k} L₂ S₂ L₃ S₃ e₂ e₃
    -----------------------------------------------
  → _,_and_,_⊢_⊆_ {i = i} {j = k} L₁ S₁ L₃ S₃ e₁ e₃
⊆-trans' x y c₁ =
  let (c₂ , eq₁₂) = x c₁
      (c₃ , eq₂₃) = y c₂
  in c₃ , Eq.trans eq₁₂ eq₂₃

≚-refl' :
  ∀ {i : Size} {A : Domain}
    {L : VarLang}
    {C : ConfLang}
    {S : Semantics L C}
    {e : L i A}
    -----------------------
  → L , S and L , S ⊢ e ≚ e
≚-refl' {i} {A} {L} {C} {e} {s} =
    ⊆-refl' {i} {A} {L} {C} {e} {s}
  , ⊆-refl' {i} {A} {L} {C} {e} {s}

≚-sym' :
  ∀ {i j : Size} {A : Domain}
    {L₁ L₂ : VarLang}
    {C₁ C₂ : ConfLang}
    {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂}
    {e₁ : L₁ i A} {e₂ : L₂ j A}
  → _,_and_,_⊢_≚_ {i = i} {j = j} L₁ S₁ L₂ S₂ e₁ e₂
    -----------------------------------------------
  → _,_and_,_⊢_≚_ {i = j} {j = i} L₂ S₂ L₁ S₁ e₂ e₁
≚-sym' (e₁⊆e₂ , e₂⊆e₁) = e₂⊆e₁ , e₁⊆e₂

≚-trans' :
  ∀ {i j k : Size} {A : Domain}
    {L₁ L₂ L₃ : VarLang}
    {C₁ C₂ C₃ : ConfLang}
    {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {S₃ : Semantics L₃ C₃}
    {e₁ : L₁ i A} {e₂ : L₂ j A} {e₃ : L₃ k A}
  → _,_and_,_⊢_≚_ {i = i} {j = j} L₁ S₁ L₂ S₂ e₁ e₂
  → _,_and_,_⊢_≚_ {i = j} {j = k} L₂ S₂ L₃ S₃ e₂ e₃
    -----------------------------------------------
  → _,_and_,_⊢_≚_ {i = i} {j = k} L₁ S₁ L₃ S₃ e₁ e₃
≚-trans'
    {i} {j} {k} {A} {L₁} {L₂} {L₃} {C₁} {C₂} {C₃} {S₁} {S₂} {S₃} {e₁} {e₂} {e₃}
    (e₁⊆e₂ , e₂⊆e₁) (e₂⊆e₃ , e₃⊆e₂)
  =
    ⊆-trans'
      {i} {j} {k} {A} {L₁} {L₂} {L₃} {C₁} {C₂} {C₃} {S₁} {S₂} {S₃} {e₁} {e₂} {e₃}
      e₁⊆e₂ e₂⊆e₃
  , ⊆-trans'
      {k} {j} {i} {A} {L₃} {L₂} {L₁} {C₃} {C₂} {C₁} {S₃} {S₂} {S₁} {e₃} {e₂} {e₁}
      e₃⊆e₂ e₂⊆e₁
```

### Relating Languages

We say that a language `L₁` is as expressive as another language `L₂` **iff** for any expression `e₂` in `L₂`, there exists an expression `e₁` in `L₁` that describes the same set of variants. This means that there exists a translation from `L₂` to `L₁`, and thus `L₁` can model `L₂`:
```agda
-- L₁ ⊇ L₂
_,_is-at-least-as-expressive-as_,_ : {C₁ C₂ : ConfLang}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → Set₁
L₁ , S₁ is-at-least-as-expressive-as L₂ , S₂ =
  ∀ {j : Size} {A : Domain} (e₂ : L₂ j A) →
    ∃-Size[ i ]
      (∃[ e₁ ∈ (L₁ i A) ]
        (L₂ , S₂ and L₁ , S₁ ⊢ e₂ ≚ e₁))

-- L₁ ⊃ L₂ ⇔ L₁ ⊇ L₂ ∧ ¬ (L₂ ⊇ L₁)
_,_is-more-expressive-than_,_ : {C₁ C₂ : ConfLang}
  → (L₁ : VarLang)
  → Semantics L₁ C₁
  → (L₂ : VarLang)
  → Semantics L₂ C₂
  → Set₁
L₁ , S₁ is-more-expressive-than L₂ , S₂ =
       L₁ , S₁ is-at-least-as-expressive-as L₂ , S₂
  × ¬ (L₂ , S₂ is-at-least-as-expressive-as L₁ , S₁)
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
    (L₁ , S₁ is-at-least-as-expressive-as L₂ , S₂)
  × (L₂ , S₂ is-at-least-as-expressive-as L₁ , S₁)
```

Expressiveness is transitive:
```agda
trans-expressiveness : ∀ {L₁ L₂ L₃ : VarLang} {C₁ C₂ C₃ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {S₃ : Semantics L₃ C₃}
  → L₁ , S₁ is-at-least-as-expressive-as L₂ , S₂
  → L₂ , S₂ is-at-least-as-expressive-as L₃ , S₃
    -----------------------------------
  → L₁ , S₁ is-at-least-as-expressive-as L₃ , S₃
trans-expressiveness
  {L₁} {L₂} {L₃}
  {C₁} {C₂} {C₃}
  {S₁} {S₂} {S₃}
  L₂→L₁ L₃→L₂ {i₃} {A} e₃
  =
  let i₂ , e₂ , e₃≚e₂ = L₃→L₂ e₃
      i₁ , e₁ , e₂≚e₁ = L₂→L₁ e₂
   in
      i₁ , e₁ ,
        ≚-trans'
          {i₃} {i₂} {i₁}
          {A}
          {L₃} {L₂} {L₁}
          {C₃} {C₂} {C₁}
          {S₃} {S₂} {S₁}
          e₃≚e₂ e₂≚e₁
```

