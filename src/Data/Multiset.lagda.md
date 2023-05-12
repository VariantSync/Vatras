# Multisubsets of Types

## Module

```agda
module Data.Multiset where
```

## Imports

```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## Definitions

```agda
Index : Set₁
Index = Set

Source : Set₁
Source = Set

Multiset : Index → Source → Set
Multiset I S = I → S

-- an element is within a subset, if there is an index pointing at that element
-- Later we could employ setoids to parameterize our set formulation in the equivalence relation instead of always relying on propositional equality.
_∈_ : ∀ {I} {S} → S → Multiset I S → Set
a ∈ A = ∃[ i ] (a ≡ A i)

-- morphisms
_⊆_ : ∀ {I J : Index} {S : Source} → Multiset I S → Multiset J S → Set
_⊆_ {I} A B = ∀ (i : I) → (A i ∈ B)

_≅_ : ∀ {I J : Index} {S : Source} → Multiset I S → Multiset J S → Set
A ≅ B = (A ⊆ B) × (B ⊆ A)
```

## Properties
```agda
⊆-refl : ∀ {I S} {A : Multiset I S}
    -----
  → A ⊆ A
⊆-refl i = i , refl

⊆-antisym : ∀ {I J S} {A : Multiset I S} {B : Multiset J S}
  → A ⊆ B
  → B ⊆ A
    -----
  → A ≅ B
⊆-antisym l r = l , r

⊆-trans : ∀ {I J K S} {A : Multiset I S} {B : Multiset J S} {C : Multiset K S}
  → A ⊆ B
  → B ⊆ C
    -----
  → A ⊆ C
⊆-trans A⊆B B⊆C i =
  let (j , ai∈B) = A⊆B i
      (k , bj∈C) = B⊆C j
   in k , Eq.trans ai∈B bj∈C

≅-refl : ∀ {I S} {A : Multiset I S}
    -----
  → A ≅ A
≅-refl = ⊆-refl , ⊆-refl

≅-sym : ∀ {I J S} {A : Multiset I S} {B : Multiset J S}
  → A ≅ B
    -----
  → B ≅ A
≅-sym (l , r) = r , l

≅-trans : ∀ {I J K S} {A : Multiset I S} {B : Multiset J S} {C : Multiset K S}
  → A ≅ B
  → B ≅ C
    -----
  → A ≅ C
≅-trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
    ⊆-trans A⊆B B⊆C
  , ⊆-trans C⊆B B⊆A
```

## Common sets and relations

```agda
{-|
The empty set
-}
𝟘 : ∀ {S} → Multiset ⊥ S
𝟘 = λ ()

{-|
The type of singleton sets over a source.
-}
𝟙 : Source → Set
𝟙 S = Multiset ⊤ S

-- predicate that checks whether a subset is nonempty
nonempty : ∀ {I} {S} → Multiset I S → Set
nonempty A = ∃[ a ] (a ∈ A)

-- predicate that checks whether a subset is empty
empty : ∀ {I} {S} → Multiset I S → Set
empty A = ¬ (nonempty A)

𝟘-is-empty : ∀ {S} → empty (𝟘 {S})
𝟘-is-empty ()

𝟘⊆A : ∀ {I S} {A : Multiset I S}
    -----
  → 𝟘 ⊆ A
𝟘⊆A = λ ()

empty-set⊆𝟘 : ∀ {I S} {A : Multiset I S}
  → empty A
    -------
  → A ⊆ 𝟘
empty-set⊆𝟘 {A = A} A-empty i with A-empty (A i , i , refl)
...| ()

all-empty-sets-are-equal : ∀ {I S}
  → (A : Multiset I S)
  → empty A
  → A ≅ 𝟘
all-empty-sets-are-equal A A-empty = empty-set⊆𝟘 A-empty , 𝟘⊆A

singleton-set-is-nonempty : ∀ {S} → (A : 𝟙 S) → nonempty A
singleton-set-is-nonempty A = A tt , tt , refl

module Examples where
  open import Data.Nat using (ℕ)
  open import Data.Fin using (Fin; suc; zero)

  ex12 : Multiset (Fin 2) ℕ
  ex12 zero = 1
  ex12 (suc zero) = 2

  ex21 : Multiset (Fin 2) ℕ
  ex21 zero = 2
  ex21 (suc zero) = 1

  12≅21 : ex12 ≅ ex21
  proj₁ 12≅21 zero = suc zero , refl
  proj₁ 12≅21 (suc zero) = zero , refl
  proj₂ 12≅21 zero = suc zero , refl
  proj₂ 12≅21 (suc zero) = zero , refl

  -- When the source is smaller than the index, then we have a multi set.
  exshrink : Multiset (Fin 2) ⊤
  exshrink x = tt
```
