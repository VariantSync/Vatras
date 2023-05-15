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
open import Data.Multiset using (Multiset; _⊆_; _≅_; ⊆-trans; ≅-trans)

open import Data.Nat using (ℕ)
open import Data.List    using (List)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Size         using (Size)

open import Relation.Nullary.Negation             using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Util.Existence                        using (∃-Size; _,_; proj₁; proj₂)

open import Definitions    using (Domain; VarLang; ConfLang; Semantics)
open import SemanticDomain using (Variant; VSet)

open import Relations.Semantic
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
Complete : LanguageProperty
Complete L C ⟦_⟧ = ∀ {A : Domain} {n : ℕ}
  → (vs : VSet n A)
    ------------------------------------------
  → ∃-Size[ i ] (Σ[ e ∈ L i A ] (vs ≅ ⟦ e ⟧))
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : LanguageProperty
Incomplete L C S = ¬ (Complete L C S)
```

## Conclusions

If a language `L₁` is complete, and another language `L₂` is as expressive as `L₁`, then also `L₂` is complete.
The intuition is that `L₂` can express everything `L₁` can express which in turn is "everything" by completeness.
Thus also `L₂` is complete.

**Proof Sketch:**
Let V be an arbitrary set of variants.
Since L₁ is complete, there exists an expression e₁ ∈ L₁ that describes V.
By assumption, L₂ is as expressive as L₁.
Thus, there exists an expression e₂ ∈ L₂ that also describes V.
Since V was picked arbitrarily, L₂ can encode any set of variants.
Thus, L₂ is complete.
```agda
completeness-by-expressiveness : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂}
  → Complete L₁ C₁ S₁
  → L₂ , S₂ is-at-least-as-expressive-as L₁ , S₁
    --------------------------------------------
  → Complete L₂ C₂ S₂
completeness-by-expressiveness encode-in-L₁ L₁-to-L₂ vs with encode-in-L₁ vs
... | i , e₁ , vs≅e₁ with L₁-to-L₂ e₁
...   | j , e₂ , e₁≅e₂ = j , e₂ , ≅-trans vs≅e₁ e₁≅e₂
```

Conversely, we can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression e of our target language L, we have to show that there exists an expression e₊ in our complete language L₊ that is variant-equivalent to e.
Given the semantics S of the complete language L of e, we compute the set of all variants described by e, as a list (THIS IS STILL LEFT TODO).
Since L₊ is complete, we can encode this list of variants in L₊, giving us an expression in e₊ in L₊ and a proof that this expression exactly describes the variants of e₋.
Now we conclude from this proof that e₊ is variant-equivalent to e₋ (TODO).
```agda
open import Data.Fin using (Fin)
postulate fooo : ∀ {L : VarLang} {C : ConfLang} {S : Semantics L C} {i : Size} {A : Domain} → (e : L i A) → ∃[ n ] (C → Fin n)

expressiveness-by-completeness : ∀ {L₊ : VarLang} {C₊ : ConfLang} {S₊ : Semantics L₊ C₊}
  → Complete L₊ C₊ S₊
  → (L : VarLang)
  → (C : ConfLang)
  → (S : Semantics L C)
    ------------------------------------------
  → L₊ , S₊ is-at-least-as-expressive-as L , S
expressiveness-by-completeness {L₊} {_} {⟦_⟧₊} L₊-comp L C ⟦_⟧
                               {_} {A} e =
  let ⟦e⟧ : C → Variant A
      ⟦e⟧ = ⟦ e ⟧

      -- variantsₑ is finite
      ⟦e⟧-fin : ∃[ n ] (Σ[ vsetₑ ∈ VSet n A ] (vsetₑ ≅ ⟦e⟧))
      ⟦e⟧-fin = {!!}

      n : ℕ
      n = proj₁ ⟦e⟧-fin

      vsetₑ : VSet n A
      vsetₑ = proj₁ (proj₂ ⟦e⟧-fin)

      vsetₑ≅⟦e⟧ : vsetₑ ≅ ⟦e⟧
      vsetₑ≅⟦e⟧ = proj₂ (proj₂ ⟦e⟧-fin)

      -- encode in L₊
      as-e₊ : ∃-Size[ i ] (Σ[ e₊ ∈ L₊ i A ] (vsetₑ ≅ ⟦ e₊ ⟧₊))
      as-e₊ = L₊-comp vsetₑ

      i : Size
      i = proj₁ as-e₊

      e₊ : L₊ i A
      e₊ = proj₁ (proj₂ as-e₊)

      vsetₑ≅⟦e₊⟧₊ : vsetₑ ≅ ⟦ e₊ ⟧₊
      vsetₑ≅⟦e₊⟧₊ = proj₂ (proj₂ as-e₊)

      -- compose proofs

      ⟦e⟧≅⟦e₊⟧₊ : ⟦ e ⟧ ≅ ⟦ e₊ ⟧₊
      ⟦e⟧≅⟦e₊⟧₊ = ≅-trans (≅-sym vsetₑ≅⟦e⟧) vsetₑ≅⟦e₊⟧₊

   in i , e₊ , ⟦e⟧≅⟦e₊⟧₊
```

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.

**Proof sketch:**
Assuming `L₋` is as expressive as `L₊`, and knowing that `L₊` is complete, we can conclude that also `L₋` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that L₋ is incomplete.
This yields a contradiction.
```agda
less-expressive-from-completeness : ∀ {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
  →   Complete L₊ C₊ S₊
  → Incomplete L₋ C₋ S₋
    --------------------------------------
  → L₋ , S₋ is-less-expressive-than L₊ , S₊
less-expressive-from-completeness L₊-comp L₋-incomp L₋-as-expressive-as-L₊ =
    L₋-incomp (completeness-by-expressiveness L₊-comp L₋-as-expressive-as-L₊)
```

Combined with `expressiveness-by-completeness` we can even further conclude that L₊ is more expressive than L₋:
```agda
more-expressive-from-completeness : ∀ {L₊ L₋ : VarLang} {C₊ C₋ : ConfLang} {S₊ : Semantics L₊ C₊} {S₋ : Semantics L₋ C₋}
  →   Complete L₊ C₊ S₊
  → Incomplete L₋ C₋ S₋
    --------------------------------------
  → L₊ , S₊ is-more-expressive-than L₋ , S₋
more-expressive-from-completeness {L₊} {L₋} {C₊} {C₋} {S₊} {S₋} L₊-comp L₋-incomp =
    expressiveness-by-completeness L₊-comp L₋ C₋ S₋
  , less-expressive-from-completeness L₊-comp L₋-incomp
```

## Translating Proofs and Analysis Results

```agda
open import Util.Existence using (∃-Size; proj₁; proj₂)
open import Data.Product using (∃-syntax; proj₁; proj₂)

VariantTheorem : (C : ConfLang) → Set₁
VariantTheorem C = ∀ {A} → (C → Variant A) → Set

bridge : ∀ {L₁ L₂ : VarLang} {C : ConfLang} {S₁ : Semantics L₁ C} {S₂ : Semantics L₂ C} {i} {A}
  → (expr : L₂ , S₂ is-at-least-as-expressive-as L₁ , S₁)
  → (thm : VariantTheorem C)
  → (e : L₁ i A)
  → thm (S₁ e)
    -----------------------------------
  → (thm (S₂ (proj₁ (proj₂ (expr e)))))
bridge L₂⊇L₁ thm e thm-e = {!!}
```
