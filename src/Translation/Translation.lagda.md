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

open import Size using (Size)

open import Data.Product   using (_,_; ∃-syntax; _×_)
open import Util.Existence using (_,_; ∃-Size; proj₁; proj₂; ∃-syntax-with-type)

open import Definitions
open import Relations.Semantic
open import SemanticDomain using (Variant)
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
record TranslationResult (A : Domain) (L₂ : VarLang) (C₁ C₂ : ConfLang) : Set where
  field
    {size} : Size
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

-- translation from a language to itself
EndoTranslation : VarLang → ConfLang → Set₁
EndoTranslation L C = Translation L L C C

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
