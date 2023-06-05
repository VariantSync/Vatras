# Definitions for Translations of Variability Languages

## Todo

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

open import Function using (_∘_)
open import Size using (Size)

open import Data.Product   using (_,_; ∃-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size; proj₁; proj₂)

open import Definitions
open import Relations.Semantic
open import Axioms.Extensionality using (_embeds-via_)
```

## Translations

A translation translates (1) a variability language `L₁` to another variability language `L₂`, as well as (2) the corresponding configuration language `C₁` to `C₂`.
The first translation is modelled as the `lang` field below while the translation of configurations is modelled by the `conf` and `fnoc` (inverse of _conf_).
A translation also has to translate configurations backwards from `C₂` to `C₁`
While this asymmetry (compared to the translation of the variability language) seems weird, the backwards translation of configurations is necessary to compare the sets of described variants of the target language `L₂` with the ones in the source language `L₁`.
For convenience, a translation also carries the semantics of the language it intends to preserve. This might not really be necessary but it purifies the below definitions.
Moreover, a translation also has to translate the size constraints over languages so that we can express that a translated expression does not become infinitely large.
```agda
record TranslationResult (A : Domain) (L₁ L₂ : VariabilityLanguage) : Set₁ where
  field
    {size} : Size
    expr   : expression L₂ size A
    conf   : configuration L₁ → configuration L₂
    fnoc   : configuration L₂ → configuration L₁
open TranslationResult public

Translation : (L₁ L₂ : VariabilityLanguage) → Set₁
Translation L₁ L₂ = ∀ {i : Size} {D : Domain} → expression L₁ i D → TranslationResult D L₁ L₂

-- translation from a language to itself
EndoTranslation : VariabilityLanguage → Set₁
EndoTranslation L = Translation L L
```

We now reformulate our relations to compare expressions between languages to translations.
An expression `e₁` describes a subset of the variants of its translated expression `lang translation e₁` if we can also translate the configuration to produce the same variant.
```agda
_⊆-via_ : ∀ {L₁ L₂ : VariabilityLanguage} {i A}
  → (e : expression L₁ i A)
  → Translation L₁ L₂
  → Set
_⊆-via_ {L₁} {L₂} {i} e₁ translate =
  let ⟦_⟧₁ = semantics L₁
      ⟦_⟧₂ = semantics L₂
  in
      ∀ (c₁ : configuration L₁) → ⟦ e₁ ⟧₁ c₁ ≡ ⟦ expr (translate e₁) ⟧₂ (conf (translate e₁) c₁)
```

From our reformulation for translations, we can indeed conclude that an expression describes a subset of the variants of its translated expression.
```agda
⊆-via→⊆ᵥ : ∀ {L₁ L₂ : VariabilityLanguage} {i A} {e₁ : expression L₁ i A}
  → (translate : Translation L₁ L₂)
  → e₁ ⊆-via translate
    -----------------------------------
  → L₁ , L₂ ⊢ e₁ ⊆ᵥ expr (translate e₁)
⊆-via→⊆ᵥ {e₁ = e₁} translate ⊆-via = λ c₁ → conf (translate e₁) c₁ , ⊆-via c₁
```

Analogously, we proceed for the inverse direction.
We cannot reuse our above definitions as we did for `_⊆-_within_and_` because we do not quantify over the second expression anymore as it is derived from applying the translation to the expression `e₁` in the source language `L₁ A`.
To check if a variant described by translated expression `lang translation e₁` is also described by the original expression `e₁`, we have to inspect whether any possible configuration of the translated expression can also be made to `e₁`.
That is the reason why we require translations to also provide backwards translations for configurations: We are not directly dealing with sets of variants but with the semantics as a function describing this set indirectly via its configuration parameter.
```agda
_⊇-via_ : ∀ {L₁ L₂ : VariabilityLanguage} {i : Size} {A : Domain}
  → (e₁ : expression L₁ i A)
  → Translation L₁ L₂
  → Set
_⊇-via_ {L₁} {L₂} e₁ translate =
  let ⟦_⟧₁ = semantics L₁
      ⟦_⟧₂ = semantics L₂
  in
    ∀ (c₂ : configuration L₂) → ⟦ e₁ ⟧₁ (fnoc (translate e₁) c₂) ≡ ⟦ expr (translate e₁) ⟧₂ c₂

-- Proof that our definition of translation is sufficient to conclude variant-subset of an expression and its translation.
⊇-via→⊆ᵥ : ∀ {L₁ L₂ : VariabilityLanguage} {i A} {e₁ : expression L₁ i A}
  → (translate : Translation L₁ L₂)
  → e₁ ⊇-via translate
    --------------------------------------------
  → L₂ , L₁ ⊢ expr (translate e₁) ⊆ᵥ e₁
⊇-via→⊆ᵥ {e₁ = e₁} translate ⊇-via = λ c₂ → fnoc (translate e₁) c₂ , Eq.sym (⊇-via c₂)
```

As earlier, we can compose the above definitions to say that an expression `e₁` describes the same set of variants as its translated expression.
```agda
_≚-via_ : ∀ {L₁ L₂ : VariabilityLanguage} {i A}
  → (e₁ : expression L₁ i A)
  → Translation L₁ L₂
  → Set
e₁ ≚-via t = e₁ ⊆-via t × e₁ ⊇-via t

≚-via→≚ : ∀ {L₁ L₂ : VariabilityLanguage} {i A} {e₁ : expression L₁ i A}
  → (translate : Translation L₁ L₂)
  → e₁ ≚-via translate
    --------------------------------------------
  → L₁ , L₂ ⊢ e₁ ≚ expr (translate e₁)
≚-via→≚ t (⊆-via , ⊇-via) =
    ⊆-via→⊆ᵥ t ⊆-via
  , ⊇-via→⊆ᵥ t ⊇-via
```

Finally, we can establish whether a translation is variant- or semantics-preserving.
A translation is variability-preserving if it translates every expression ot a variant-equivalent expression.
This is one of the major theorems we ought to show for translation between variability languages.
```agda
_is-variant-preserving : ∀ {L₁ L₂ : VariabilityLanguage} → Translation L₁ L₂ → Set₁
_is-variant-preserving {L₁} t = ∀ {A : Domain} → (e₁ : Expression A L₁) → (get e₁) ≚-via t
```

A translation is semantics preserving iff its semantics preserving and the same configuration yields the same variants.
We identify a configuration to be the same if it can be uniquely translated back (i.e., if `conf` is an embedding into `C₂` via its inverse `fnoc`).
We do not require the inverse direction (`fnoc` being an embedding of configurations from `C₂` into `C₁`) because `C₂` could be larger than `C₁` (when interpreted as a set).
For example, the set of features in `C₂` could be bigger (e.g., when going from core choice calculus to binary choice calculus) but all information can be derived by `conf` from our initial configuration `c₁`.
```agda
_is-semantics-preserving : ∀ {L₁ L₂ : VariabilityLanguage} → Translation L₁ L₂ → Set₁
_is-semantics-preserving {L₁ = L₁} translate =
    translate is-variant-preserving
  × (∀ {A : Domain} (e₁ : Expression A L₁) → (conf (translate (get e₁))) embeds-via (fnoc (translate (get e₁))))
```

We can conclude that a language is as expressive as another language if there exists a variant preserving translation.
This is our major theorem that allows us to prove relations about languages from writing translations.
```agda
expressiveness-by-translation : ∀ {L₁ L₂ : VariabilityLanguage}
  → (translate : Translation L₁ L₂)
  → translate is-variant-preserving
    ----------------------------------
  → L₂ is-at-least-as-expressive-as L₁
expressiveness-by-translation {_} {L₂} translate preservation e₁ =
  let r = translate (get e₁) in
  fromExpression L₂ (expr r) , ≚-via→≚ translate (preservation e₁)
```
