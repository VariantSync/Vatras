# Clone-and-Own as a Variability Language

The simples way to express variability is to just list all the alternatives.
In software engineering, developing software like this is know as _clone-and-own_.
Formally, expressing variability in this way amounts to declaring a list of variants.

## Module

```agda
open import Framework.Definitions
module Lang.VariantList (V : 𝕍) where
```

## Imports

```agda
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List as List using ([]; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Function using (_∘_; Surjective)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)

open import Framework.VariabilityLanguage
open import Framework.Properties.Completeness V using (Complete)
open import Framework.Properties.Soundness V using (Sound)
open import Framework.Properties.Finity V using (soundness-from-enumerability)
open import Framework.Relation.Configuration V using (_∋_⊢_≣ⁱ_)
open import Data.EqIndexedSet as ISet
open import Util.List using (find-or-last)
```

## Syntax

```agda
VariantList : 𝔼
VariantList A = List⁺ (V A)

{-|
Just an alias.
-}
Clone-and-Own : 𝔼
Clone-and-Own = VariantList
```

## Semantics

```agda
{-|
To obtain a variant, we have to do a list lookup.
Hence, a configuration is just an index / address in that list.
For simplicity, we allow just any natural number and just pick the
last variant in case of an overview.
Otherwise, the type of configuration must be parameterized in the
particular expression to configure.
-}
Configuration : ℂ
Configuration = ℕ

{-|
Semantics is just a list lookup.
-}
-- ⟦_⟧ : ∀ {i : Size} {A : 𝔸} → VariantList i A → Configuration → Variant i A
⟦_⟧ : 𝔼-Semantics V Configuration VariantList
⟦ clones ⟧ i = find-or-last i clones
```

## Clone-and-Own as a Variability Language

```agda
VariantListL : VariabilityLanguage V
VariantListL = ⟪ VariantList , Configuration , ⟦_⟧ ⟫
```

## Properties

We now prove completeness and soundness of clone-and-own.
These proofs will form the basis for proving these properties for other languages as well.

### Completeness

To prove completeness, we have to show that lists of variants can express any variant map.

```agda
open import Util.Nat.AtLeast using (cappedFin)

private
  open import Framework.VariantMap V
  variable
    n : ℕ
    A : 𝔸
    e : VariantList A

-- rules for translating a variant map to a list of variants
infix 3 _⊢_⟶_
data _⊢_⟶_ : ∀ (n : ℕ) → VMap A n → VariantList A → Set₁ where
  -- a singleton set is translated to a singleton list
  E-zero : ∀ {A} {V : VMap A zero}
      ------------------------
    → zero ⊢ V ⟶ V zero ∷ []

  {-|
  For a set V with more than one variant, we:
  - put the first variant into our list
  - remove that first variant from our set of variants
  - translate the rest recursively.
  -}
  E-suc : ∀ {V : VMap A (suc n)}
    → n ⊢ remove-first A V ⟶ e
      -------------------------------
    → suc n ⊢ V ⟶ V zero ∷ toList e

{-| Proof that the encoding is deterministic -}
determinism : ∀ {e₁ e₂ : VariantList A} {V : VMap A n}
  → n ⊢ V ⟶ e₁
  → n ⊢ V ⟶ e₂
    -----------------
  → e₁ ≡ e₂
determinism E-zero E-zero = refl
determinism (E-suc l) (E-suc r) rewrite determinism l r = refl

-- smart constructor for totality proofs
-- makes the implicit result expression e explicit
return : ∀ {V : VMap A n}
  →         n ⊢ V ⟶ e
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
return {e = e} ⟶e = e , ⟶e

{-| Proof that the encoding is total and thus can be computed. -}
total :
  ∀ (V : VMap A n)
    --------------------
  → ∃[ e ] (n ⊢ V ⟶ e)
total {n = zero}  vs = return E-zero
total {n = suc n} vs = return (E-suc (proj₂ (total (remove-first _ vs))))

{-| Encodes a set of variants into a list of variants. -}
encode : VMap A n → VariantList A
encode = proj₁ ∘ total

-- translate configs

vl-conf : Fin (suc n) → Configuration
vl-conf i = toℕ i

vl-fnoc : Configuration → Fin (suc n)
vl-fnoc c = cappedFin c

-- prove preservation of the encoding

preserves-∈ : ∀ {V}
  → n ⊢ V ⟶ e
    ---------------------
  → V ⊆[ vl-conf ] ⟦ e ⟧
preserves-∈ E-zero    zero = refl

preserves-∈ (E-suc _) zero = refl
preserves-∈ (E-suc ⟶e) (suc i) = preserves-∈ ⟶e i

preserves-∋ : ∀ {V}
  → n ⊢ V ⟶ e
    ---------------------
  → ⟦ e ⟧ ⊆[ vl-fnoc ] V
preserves-∋ E-zero      zero   = refl
preserves-∋ E-zero     (suc _) = refl
preserves-∋ (E-suc  _)  zero   = refl
preserves-∋ (E-suc ⟶e) (suc c) = preserves-∋ ⟶e c

preserves : ∀ {V}
  → n ⊢ V ⟶ e
    ----------
  → V ≅ ⟦ e ⟧
preserves encoding = ≅[]→≅ (preserves-∈ encoding , preserves-∋ encoding)

-- final completeness proof
VariantList-is-Complete : Complete VariantListL
VariantList-is-Complete vs =
  let e , derivation = total vs
  in  e , preserves derivation
```

### Soundness

By proving that `vl-conf` is the inverse of `vl-fnoc`, we can reuse our encoding above to prove soundness as well:

```agda
-- vl-conf is inverse to vl-fnoc w.r.t. semantic equivalence of configurations.
inverse : ∀ {A} (c : Configuration) (e : VariantList A) → VariantListL ∋ e ⊢ vl-conf {length e} (vl-fnoc c) ≣ⁱ c
inverse zero e = refl
inverse (suc c) (_ ∷ []) = refl
inverse (suc c) (_ ∷ y ∷ ys) = inverse c (y ∷ ys)

VariantList-is-Sound : Sound VariantListL
VariantList-is-Sound e =
    length e
  , ⟦ e ⟧ ∘ vl-conf
  , (λ i → vl-conf i , refl)
  , (λ i → vl-fnoc i , sym (inverse i e))
```

## Show

```agda
open import Data.String as String using (String; _++_; intersperse)
open import Data.Product using (_,_)
open import Show.Lines

pretty : {A : 𝔸} → (V A → String) → VariantList A → Lines
pretty {A} pretty-variant (v ∷ vs) = do
  > "[ " ++ pretty-variant v
  lines (List.map (λ v → > ", " ++ pretty-variant v) vs)
  > "]"
```
