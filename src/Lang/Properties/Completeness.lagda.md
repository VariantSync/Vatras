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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Data.List.Relation.Unary.All          using (All)
                                                  renaming (map to mapAll)
open import Data.List.Relation.Unary.Any          using (Any)
                                                  renaming (map to mapAny)
open import Util.Existence                        using (∃-Size; ∃-syntax-with-type; _,_)

open import Definitions    using (Domain; VarLang; ConfLang; Semantics)
open import SemanticDomain using (Variant)

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

_,_,_⊢_describes-exactly_ : ∀ {i : Size} {A : Domain}
  → (L : VarLang)
  → (C : ConfLang)
  → Semantics L C
  → L i A
  → List (Variant A)
  → Set
L , C , S ⊢ e describes-exactly vs =
    L , C , S ⊢ e describes-all vs
  × L , C , S ⊢ vs contains-all e

Complete : LanguageProperty
Complete L C S =
  ∀ {A : Domain}
    (vs : List (Variant A))
    -----------------------
  → ∃-Size[ i ] (
      ∃[ e ∈ (L i A)] (
        L , C , S ⊢ e describes-exactly vs
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
{-
When an expression e₁ ∈ L₁ describes all variants vs
and e₁ describes the same set of variants as e₂ ∈ L₂
then we can conclude that e₂ also describes all variants vs.
-}
subst-e-describes-all-vs : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {i j : Size} {A : Domain}
  → (vs : List (Variant A))
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → L₁ , S₁ and L₂ , S₂ ⊢ e₁ ≚ e₂
  → L₁ , C₁ , S₁        ⊢ e₁ describes-all vs
    ------------------------------------------
  → L₂ , C₂ , S₂        ⊢ e₂ describes-all vs
subst-e-describes-all-vs vs e₁ e₂ e₁≚e₂ e₁-describes-vs =
  let (e₁⊆e₂ , e₂⊆e₁) = e₁≚e₂
   in
      {-
      e₁-describes-vs is a list of proofs, each one proving that e₁
      describes a particular variant v in vs.
      We transform each of these proofs into a proof that also e₂
      describes that variant v.
      -}
      mapAll (
        {-
        A proof that e₁ describes v consists of a configuration c₁ and a proof
        that c₁ configures e₁ to v in the given semantics S₁ (not in scope).
        -}
        λ (c₁ , ⟦e₁⟧c₁≡v) →
          {-
          Since we know that e₁ describes the same set of variants as e₂ (via e₁≚e₂)
          we also know that all variants described by e₁ are also described by e₂ (via e₁⊆e₂).
          In particular, for every configuration that configures e₁, there is a corresponding
          configuration that configures e₂ to the same variant.
          Since we know that c₁ configures e₁ to v, we can conclude that there exists a corresponding
          configuration c₂ that configures e₂ to the same variant (via ⟦e₁⟧c₁≡⟦e₂⟧c₂).
          -}
          let (c₂ , ⟦e₁⟧c₁≡⟦e₂⟧c₂) = e₁⊆e₂ c₁
           in
               {-
               By transitivity, we see that c₂ is a suitable configuration for e₂ to obtain v:
               We know that c₂ configures e₂ to the same variant e₁ is configured to by c₁ (via ⟦e₁⟧c₁≡⟦e₂⟧c₂) which in turn is v (via ⟦e₁⟧c₁≡v).
               So we pick c₂.
               -}
                c₂
                {-
                Following the same transitive reasoning as above, we can prove that c₂ indeed configures e₂ to v.
                We first flip ⟦e₁⟧c₁≡⟦e₂⟧c₂ using sym to find ⟦e₂⟧c₂≡⟦e₁⟧c₁,
                which we can glue to ⟦e₁⟧c₁≡v via transitivity to obtain a proof for ⟦e₂⟧ c₂ ≡ v.
                -}
              , trans (sym ⟦e₁⟧c₁≡⟦e₂⟧c₂) ⟦e₁⟧c₁≡v
      ) e₁-describes-vs

subst-vs-contains-all-e : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂} {i j : Size} {A : Domain}
  → (vs : List (Variant A))
  → (e₁ : L₁ i A)
  → (e₂ : L₂ j A)
  → L₁ , S₁ and L₂ , S₂ ⊢ e₁ ≚ e₂
  → L₁ , C₁ , S₁ ⊢ vs contains-all e₁
    -----------------------------------
  → L₂ , C₂ , S₂ ⊢ vs contains-all e₂
subst-vs-contains-all-e vs e₁ e₂ e₁≚e₂ vs-contains-e₁  =
  {-
  Our goal is to show that for any configuration c₂ always configures e₂ to a variant in vs.
  So given any c₂ ...
  -}
  λ c₂ →
    {-
    ... we know that there must exist a c₁ that configures e₁ to the same variant e₂ is configured to by c₂.
    We know this because we know that e₁ and e₂ describe the same set of variants (via e₁≚e₂)
    -}
    let (e₁⊆e₂ , e₂⊆e₁) = e₁≚e₂
        c₁ , ⟦e₂⟧c₂≡⟦e₁⟧c₁ = e₂⊆e₁ c₂
     in
        {-
        We also know (via vs-contains-e₁) that for any configuration, e₁ is always configured to a variant in vs.
        So it is for c₁ in particular.
        By application vs-contains-e₁ c₁ we obtain a proof that there exists at least one variant in vs
        that is equal to ⟦ e₁ ⟧ c₁ (i.e., we get an Any instance).
        Using mapAny, we convert the proof that any variant satisfying ⟦e₁⟧c₁≡v is also obtained by configuring e₂ with c₂.
        We can conclude this by transitivity, knowing that ⟦e₂⟧c₂≡⟦e₁⟧c₁.
        -}
        mapAny (
          λ ⟦e₁⟧c₁≡v → trans ⟦e₂⟧c₂≡⟦e₁⟧c₁ ⟦e₁⟧c₁≡v
        ) (vs-contains-e₁ c₁)

completeness-by-expressiveness : ∀ {L₁ L₂ : VarLang} {C₁ C₂ : ConfLang} {S₁ : Semantics L₁ C₁} {S₂ : Semantics L₂ C₂}
  → Complete L₁ C₁ S₁
  → L₂ , S₂ is-as-expressive-as L₁ , S₁
    -----------------------------------
  → Complete L₂ C₂ S₂
completeness-by-expressiveness {L₁} {L₂} {_} {_} {S₁} {S₂} encode-in-L₁ L₁-to-L₂ vs =
  let {-
      Given an arbitrary set of variants vs, we can encode it in L₁ since L₁ is complete.
      This gives us an expression e₁ of size i and a proof that e₁ describes exactly the variants vs,
      which breaks down to two proofs:
      - e₁-describes-vs proving that e₁ describes at least the variants in vs, and
      - vs-contains-e₁  proving that any variant described by e₁ is a variant in vs.
      -}
      i , e₁ , e₁-describes-vs , vs-contains-e₁
        = encode-in-L₁ vs
      {-
      Given that L₂ is as expressive as L₁, we know that there exists a variant-equivalent expression e₂ in L₂
      for our expression e₁.
      We get that expression e₂, its size j, and a proof that e₂ is variant-equivalent to e₁.
      -}
      j , e₂ , e₂-describes-what-e₁-describes
        = L₁-to-L₂ e₁
   in
      {-
      To prove the completeness of L₂, we now have to show that e₂ of size j
      1. describes at least the variants vs
      2. describes at most the variants vs
      which we do by substituting e₂ for e₁ in the respective proofs above.
      -}
        j
      , e₂
      , subst-e-describes-all-vs {L₁ = L₁} {L₂ = L₂} {S₁ = S₁} {S₂ = S₂} vs e₁ e₂ e₂-describes-what-e₁-describes e₁-describes-vs
      , subst-vs-contains-all-e  {L₁ = L₁} {L₂ = L₂} {S₁ = S₁} {S₂ = S₂} vs e₁ e₂ e₂-describes-what-e₁-describes vs-contains-e₁
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


