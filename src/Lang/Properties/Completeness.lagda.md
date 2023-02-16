# Completeness and Incompleteness of Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Lang.Properties.Completeness where
```

## Imports

```agda
open import Data.List    using (List)
open import Data.Product using (_×_; _,_)
open import Size         using (Size)

open import Relation.Nullary.Negation             using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List.Relation.Unary.All          using (All)
open import Data.List.Relation.Unary.Any          using (Any)
open import Util.Existence                        using (∃-Size; ∃-syntax-with-type; _,_)

open import Definitions    using (Domain; VarLang; ConfLang; Semantics)
open import SemanticDomain using (Variant)
```

## Definitions

A property of a language is predicate over the variability language, its corresponding configuration language, and the semantics:
```agda
LanguageProperty : Set₂
LanguageProperty = ∀ (L : VarLang) → (C : ConfLang) → Semantics L C → Set₁
```

Completess is given iff for any set of variants `vs` (modelled as a list for convenience in Agda), there exists an expression `e` in the language `L` that describes all variants in `v`.
In particular, for every variant `v` in `vs`, there exists a configuration `c` that configures `e` to `v`.
```agda
_∈_ : ∀ {A : Set} → A → List A → Set
a ∈ as = Any (λ a' → a ≡ a') as

_,_,_⊢_describes-all_ : ∀ {i : Size} {A : Domain}
  → (L : VarLang)
  → (C : ConfLang)
  → Semantics L C
  → L i A
  → List (Variant A)
  → Set
L , C , ⟦_⟧ ⊢ e describes-all vs = All (λ v → ∃[ c ∈ C ] (⟦ e ⟧ c ≡ v)) vs

_,_,_⊢_contains-all_ : ∀ {i : Size} {A : Domain}
  → (L : VarLang)
  → (C : ConfLang)
  → Semantics L C
  → List (Variant A)
  → L i A
  → Set
L , C , ⟦_⟧ ⊢ vs contains-all e = ∀ (c : C) → ⟦ e ⟧ c ∈ vs

Complete : LanguageProperty
Complete L C S =
  ∀ {A : Domain}
    (vs : List (Variant A))
    -----------------------
  → ∃-Size[ i ] (
      ∃[ e ∈ (L i A)] (
          (L , C , S ⊢ e describes-all vs)
        × (L , C , S ⊢ vs contains-all e)
      )
    )
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : LanguageProperty
Incomplete L C S = ¬ (Complete L C S)
```

## Conclusions

If a language `L₁` is complete, and another language `L₂` is complete, then also `L₂` is complete.

**Proof Sketch:**
Let V be an arbitrary set of variants.
Since L₊ is complete, there exists an expression e₊ ∈ L₊ that describes V.
By assumption, L₋ is as expressive as L₊.
Thus, there exists an expression e₋ ∈ L₋ that also describes V.
Since V was picked arbitrarily, L₋ can encode any set of variants.
Thus, L₋ is complete.
```agda
open import Relations.Semantic

-- TODO: Find proper names for foo and bar.
foo : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {i j : Size} {A : Domain}
  → (vs : List (Variant A))
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → L₁ , C₁ , S₁ ⊢ e₁ describes-all vs
  → L₁ , S₁ and L₂ , S₂ ⊢ e₁ ≚ e₂
    -----------------------------------
  → L₂ , C₂ , S₂ ⊢ e₂ describes-all vs
foo vs e₁ e₂ e₁-describes-vs e₁≚e₂ = {!!}

bar : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {i j : Size} {A : Domain}
  → (vs : List (Variant A))
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → L₁ , C₁ , S₁ ⊢ vs contains-all e₁
  → L₁ , S₁ and L₂ , S₂ ⊢ e₁ ≚ e₂
    -----------------------------------
  → L₂ , C₂ , S₂ ⊢ vs contains-all e₂
bar vs e₁ e₂ vs-contains-e₁ e₁≚e₂ = {!!}

completeness-by-expressiveness : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂}
  → Complete L₁ C₁ S₁
  → L₂ , S₂ is-as-expressive-as L₁ , S₁
    -----------------------------------
  → Complete L₂ C₂ S₂
completeness-by-expressiveness {L₁} {L₂} {_} {_} {S₁} {S₂} encode-in-L₁ L₁-to-L₂ vs =
  let i , e₁ , e₁-describes-vs , vs-contains-e₁
        = encode-in-L₁ vs
      j , e₂ , e₂-describes-what-e₁-describes
        = L₁-to-L₂ e₁
   in
        j
      , e₂
      , foo {L₁ = L₁} {L₂ = L₂} {S₁ = S₁} {S₂ = S₂} vs e₁ e₂ e₁-describes-vs e₂-describes-what-e₁-describes
      , bar {L₁ = L₁} {L₂ = L₂} {S₁ = S₁} {S₂ = S₂} vs e₁ e₂ vs-contains-e₁  e₂-describes-what-e₁-describes
```

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.

**Proof sketch:**
Assuming `L₋` is as expressive as `L₊`, and knowing that `L₊` is complete, we can conclude that also `L₋` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that L₋ is incomplete.
This yields a contradiction.
```agda
less-expressive : ∀ {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
  →   Complete L₊ C₊ S₊
  → Incomplete L₋ C₋ S₋
    --------------------------------------
  → ¬ (L₋ , S₋ is-as-expressive-as L₊ , S₊)
less-expressive L₊-comp L₋-incomp L₋-as-expressive-as-L₊ =
    L₋-incomp (completeness-by-expressiveness L₊-comp L₋-as-expressive-as-L₊)
```

Hence, there cannot be a variant-preserving translation `L₊ → L₋`.
```agda
open import Translation.Translation --using (Translation; _is-variant-preserving)

-- untranslateable : ∀ {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
--   → Complete L₊ C₊ S₊
--   → Incomplete L₋ C₋ S₋
--   → (t : Translation L₊ L₋ C₊ C₋)
--   → sem₁ t e ≡ S₊ e
-- --  → sem₂ t ≡ S₋
--   → ¬ (t is-variant-preserving)
-- untranslateable = {!!}
```


