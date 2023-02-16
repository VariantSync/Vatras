# Completeness and Incompleteness of Variability Languages

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Lang.Properties.Completeness where
```

## Imports

```agda
open import Data.List using (List)
open import Size      using (Size)

open import Relation.Nullary.Negation             using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List.Relation.Unary.All          using (All)
open import Util.Existence                        using (∃-Size; ∃-syntax-with-type)

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
_,_,_⊢_describes-all_ : ∀ {i : Size} {A : Domain}
  → (L : VarLang)
  → (C : ConfLang)
  → Semantics L C
  → L i A
  → List (Variant A)
  → Set
L , C , ⟦_⟧ ⊢ e describes-all vs = All (λ v → ∃[ c ∈ C ] (⟦ e ⟧ c ≡ v)) vs

Complete : LanguageProperty
Complete L C S =
  ∀ {A : Domain}
    (vs : List (Variant A))
    -----------------------
  → ∃-Size[ i ] (
      ∃[ e ∈ (L i A)] (
        L , C , S ⊢ e describes-all vs
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

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.
```agda
open import Relations.Semantic

less-expressive : ∀ {i : Size} {A : Domain} {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
  →   Complete L₊ C₊ S₊
  → Incomplete L₋ C₋ S₋
    --------------------------------------
  → ¬ (L₋ , S₋ is-as-expressive-as L₊ , S₊)
{-
Proof idea:
Let V be an arbitrary set of variants.
Since L₊ is complete, there exists an expression e₊ ∈ L₊ that describes V.
By assumption, L₋ is as expressive as L₊.
Thus, there exists an expression e₋ ∈ L₋ that also describes V.
Since V was picked arbitrarily, L₋ can encode any set of variants.
Thus, L₋ is complete.
Yet, we already know that L₋ is incomplete.
Contradiction ∎
-}
less-expressive L₊-comp L₋-incomp L₋-as-expressive-as-L₊ = {!!}
```

Hence, there cannot be a variant-preserving translation `L₊ → L₋`.
```agda
open import Translation.Translation --using (Translation; _is-variant-preserving)

-- untranslateable : ∀ {i : Size} {A : Domain} {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
--   → Complete L₊ C₊ S₊
--   → Incomplete L₋ C₋ S₋
--   → (t : Translation L₊ L₋ C₊ C₋)
--   → (∀ (i : Size) (e : L₊ i A) → sem₁ t e ≡ S₊ e)
-- --  → sem₂ t ≡ S₋
--   → ¬ (t is-variant-preserving)
-- untranslateable = {!!}
```


