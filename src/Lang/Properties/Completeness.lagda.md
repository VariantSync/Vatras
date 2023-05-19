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
open import Data.Nat using (ℕ)
open import Data.List    using (List)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Size         using (Size)

open import Relation.Nullary.Negation             using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Util.Existence                        using (∃-Size; _,_; proj₁; proj₂)

open import Definitions   -- using (Domain; FeatureLang; SelectionLang; VarLang; VSet; Semantics; VariabilityLanguage; Expression; semantics; get; fromExpression)
-- open import SemanticDomain using (Variant)

open import Relations.Semantic

import Relation.Binary.PropositionalEquality as Eq

import Data.Multiset as MSet
--open import Data.Multiset using (Multiset; _⊆_; _≅_; ⊆-trans; ≅-trans; ≅-sym)

--open MSet (VariantSetoid A) using (Multiset; _⊆_; _≅_; ⊆-trans; ≅-trans; ≅-sym)
```

## Definitions

Completess is given iff for any set of variants `vs` (modelled as a list for convenience in Agda), there exists an expression `e` in the language `L` that describes all variants in `v`.
In particular, for every variant `v` in `vs`, there exists a configuration `c` that configures `e` to `v`.
```agda
Complete : VariabilityLanguage → Set₁
Complete L = ∀ {A : Domain} {F : FeatureLang} {S : SelectionLang}
  → (vs : VSet F S A)
    ----------------------------------
  → Σ[ e ∈ Expression A L ]
      (let open MSet (VariantSetoid A)
           ⟦_⟧ = semantics L
        in vs ≅ ⟦ get e ⟧)
```

We define incompleteness as then negation of completeness.
This means assuming completeness for a language yields a contradiction.
```agda
Incomplete : VariabilityLanguage → Set₁
Incomplete L = ¬ (Complete L)
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
completeness-by-expressiveness : ∀ {L₁ L₂ : VariabilityLanguage}
  → Complete L₁
  → L₂ is-at-least-as-expressive-as L₁
    --------------------------------------------
  → Complete L₂
completeness-by-expressiveness encode-in-L₁ L₁-to-L₂ vs with encode-in-L₁ vs
... | e₁ , vs≅e₁ with L₁-to-L₂ e₁
...   | e₂ , e₁≅e₂ = e₂ , ≅-trans vs≅e₁ e₁≅e₂
  where open MSet (VariantSetoid _) using (≅-trans)
```

Conversely, we can conclude that any complete language is at least as expressive as any other variability language.

**Proof sketch:**
Given an arbitrary expression e of our target language L, we have to show that there exists an expression e₊ in our complete language L₊ that is variant-equivalent to e.
Given the semantics S of the complete language L of e, we compute the set of all variants described by e, as a list (THIS IS STILL LEFT TODO).
Since L₊ is complete, we can encode this list of variants in L₊, giving us an expression in e₊ in L₊ and a proof that this expression exactly describes the variants of e₋.
Now we conclude from this proof that e₊ is variant-equivalent to e₋ (TODO).
```agda
expressiveness-by-completeness : ∀ {L₊ : VariabilityLanguage}
  → Complete L₊
  → (L : VariabilityLanguage)
    ---------------------------------
  → L₊ is-at-least-as-expressive-as L
expressiveness-by-completeness L₊-comp L e = L₊-comp ⟦ get e ⟧
                               where ⟦_⟧ = semantics L
  -- let ⟦e⟧ : Configuration C → Variant A
  --     ⟦e⟧ = ⟦ e ⟧

  --     -- variantsₑ is finite
  --     ⟦e⟧-fin : ∃[ n ] (Σ[ vsetₑ ∈ VSet n A ] (vsetₑ ≅ ⟦e⟧))
  --     ⟦e⟧-fin = {!!}

  --     n : ℕ
  --     n = proj₁ ⟦e⟧-fin

  --     vsetₑ : VSet n A
  --     vsetₑ = proj₁ (proj₂ ⟦e⟧-fin)

  --     vsetₑ≅⟦e⟧ : vsetₑ ≅ ⟦e⟧
  --     vsetₑ≅⟦e⟧ = proj₂ (proj₂ ⟦e⟧-fin)

  --     -- encode in L₊
  --     as-e₊ : ∃-Size[ i ] (Σ[ e₊ ∈ L₊ i A ] (vsetₑ ≅ ⟦ e₊ ⟧₊))
  --     as-e₊ = L₊-comp 

  --     i : Size
  --     i = proj₁ as-e₊

  --     e₊ : L₊ i A
  --     e₊ = proj₁ (proj₂ as-e₊)

  --     vsetₑ≅⟦e₊⟧₊ : vsetₑ ≅ ⟦ e₊ ⟧₊
  --     vsetₑ≅⟦e₊⟧₊ = proj₂ (proj₂ as-e₊)

  --     -- compose proofs

  --     ⟦e⟧≅⟦e₊⟧₊ : ⟦ e ⟧ ≅ ⟦ e₊ ⟧₊
  --     ⟦e⟧≅⟦e₊⟧₊ = ≅-trans (≅-sym vsetₑ≅⟦e⟧) vsetₑ≅⟦e₊⟧₊

  --  in i , e₊ , ⟦e⟧≅⟦e₊⟧₊
```

If a language `L₊` is complete and another language `L₋` is incomplete then `L₋` less expressive than `L₊`.

**Proof sketch:**
Assuming `L₋` is as expressive as `L₊`, and knowing that `L₊` is complete, we can conclude that also `L₋` is complete (via `completeness-by-exoressiveness` above).
Yet, we already know that L₋ is incomplete.
This yields a contradiction.
```agda
less-expressive-from-completeness : ∀ {L₊ L₋ : VariabilityLanguage}
  →   Complete L₊
  → Incomplete L₋
    --------------------------------------
  → L₋ is-less-expressive-than L₊
less-expressive-from-completeness L₊-comp L₋-incomp L₋-as-expressive-as-L₊ =
    L₋-incomp (completeness-by-expressiveness L₊-comp L₋-as-expressive-as-L₊)
```

Combined with `expressiveness-by-completeness` we can even further conclude that L₊ is more expressive than L₋:
```agda
more-expressive-from-completeness : ∀ {L₊ L₋ : VariabilityLanguage}
  →   Complete L₊
  → Incomplete L₋
    --------------------------------------
  → L₊ is-more-expressive-than L₋
more-expressive-from-completeness {L₊} {L₋} L₊-comp L₋-incomp =
    expressiveness-by-completeness L₊-comp L₋
  , less-expressive-from-completeness L₊-comp L₋-incomp
```

## Translating Proofs and Analysis Results

```agda
open import Util.Existence using (∃-Size; proj₁; proj₂)
open import Data.Product using (∃-syntax; proj₁; proj₂)

-- VariantTheorem : (C : ConfLang) → Set₁
-- VariantTheorem C = ∀ {A} → (C → Variant A) → Set

-- bridge : ∀ {L₁ L₂ : VarLang} {C : ConfLang} {S₁ : Semantics L₁ C} {S₂ : Semantics L₂ C} {i} {A}
--   → (expr : L₂ , S₂ is-at-least-as-expressive-as L₁ , S₁)
--   → (thm : VariantTheorem C)
--   → (e : L₁ i A)
--   → thm (S₁ e)
--     -----------------------------------
--   → (thm (S₂ (proj₁ (proj₂ (expr e)))))
-- bridge L₂⊇L₁ thm e thm-e = {!!}
```
