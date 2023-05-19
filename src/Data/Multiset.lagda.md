# Multisubsets of Types

## Module

```agda
{-# OPTIONS --allow-unsolved-metas #-}

open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (
  Setoid;
  Antisym;
  IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous using (
  IRel;
  Reflexive;
  Symmetric;
  Transitive;
  IsIndexedEquivalence)
module Data.Multiset
  {c ℓ : Level}
  (S : Setoid c ℓ)
  where
```

## Imports

```agda
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open Setoid S
module Eq = IsEquivalence isEquivalence
```

## Definitions

```agda
Index : Set (suc c)
Index = Set c

Multiset : Index → Set c
Multiset I = I → Carrier

-- an element is within a subset, if there is an index pointing at that element
-- Later we could employ setoids to parameterize our set formulation in the equivalence relation instead of always relying on propositional equality.
_∈_ : ∀ {I} → Carrier → Multiset I → Set (c ⊔ ℓ)
a ∈ A = ∃[ i ] (a ≈ A i)

-- morphisms
-- _⊆_ : ∀ {I J} → Multiset I → Multiset J → Set ℓ
_⊆_ : IRel Multiset (c ⊔ ℓ)
_⊆_ {I} A B = ∀ (i : I) → A i ∈ B

_≅_ : IRel Multiset (c ⊔ ℓ)
A ≅ B = (A ⊆ B) × (B ⊆ A)
```

## Properties
```agda
⊆-refl : Reflexive Multiset _⊆_
⊆-refl i = i , Eq.refl

-- Todo: There is no antsymmetry definition in Relation.Binary.Indexed.Heterogeneous.Definition. Adding that to the standard library would be good and a low hanging fruit.
⊆-antisym : ∀ {I J} → Antisym (_⊆_ {I} {J}) (_⊆_ {J} {I}) (_≅_ {I} {J})
⊆-antisym l r = l , r

⊆-trans : Transitive Multiset _⊆_
⊆-trans A⊆B B⊆C i =
  let (j , Ai≈Bj) = A⊆B i
      (k , Bj≈Ck) = B⊆C j
   in k , Eq.trans Ai≈Bj Bj≈Ck

≅-refl : Reflexive Multiset _≅_
≅-refl = ⊆-refl , ⊆-refl

≅-sym : Symmetric Multiset _≅_
≅-sym (l , r) = r , l

≅-trans : Transitive Multiset _≅_
≅-trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
    ⊆-trans A⊆B B⊆C
  , ⊆-trans C⊆B B⊆A

≅-IsIndexedEquivalence : IsIndexedEquivalence Multiset _≅_
≅-IsIndexedEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }
```

## Common sets and relations

```agda
{-|
The empty set
-}
𝟘 : Multiset ⊥
𝟘 = λ ()

{-|
The type of singleton sets over a source.
-}
𝟙 : Set c
𝟙 = Multiset ⊤

-- predicate that checks whether a subset is nonempty
nonempty : ∀ {I} → Multiset I → Set (c ⊔ ℓ)
nonempty A = ∃[ a ] (a ∈ A)

-- predicate that checks whether a subset is empty
empty : ∀ {I} → Multiset I → Set (c ⊔ ℓ)
empty A = ¬ (nonempty A)

𝟘-is-empty : empty 𝟘
𝟘-is-empty ()

𝟘⊆A : ∀ {I} {A : Multiset I}
    -----
  → 𝟘 ⊆ A
𝟘⊆A = λ ()

empty-set⊆𝟘 : ∀ {I} {A : Multiset I}
  → empty A
    -------
  → A ⊆ 𝟘
empty-set⊆𝟘 {A = A} A-empty i with A-empty (A i , i , Eq.refl)
...| ()

all-empty-sets-are-equal : ∀ {I} {A : Multiset I}
  → empty A
  → A ≅ 𝟘
all-empty-sets-are-equal A-empty = empty-set⊆𝟘 A-empty , 𝟘⊆A

singleton-set-is-nonempty : (A : 𝟙) → nonempty A
singleton-set-is-nonempty A = A tt , tt , Eq.refl

-- module Examples where
--   open import Data.Nat using (ℕ)
--   open import Data.Fin using (Fin; suc; zero)
--   open import Relation.Binary.PropositionalEquality as Peq
--   open Level using (0ℓ)

--   ex12 : Multiset ℕ Peq.isEquivalence (Fin 2)
--   ex12 zero = 1
--   ex12 (suc zero) = 2

--   ex21 : Multiset (Fin 2) ℕ
--   ex21 zero = 2
--   ex21 (suc zero) = 1

--   12≅21 : ex12 ≅ ex21
--   proj₁ 12≅21 zero = suc zero , Eq.refl
--   proj₁ 12≅21 (suc zero) = zero , Eq.refl
--   proj₂ 12≅21 zero = suc zero , Eq.refl
--   proj₂ 12≅21 (suc zero) = zero , Eq.refl

--   -- When the source is smaller than the index, then we have a multi set.
--   exshrink : Multiset (Fin 2) ⊤
--   exshrink x = tt
```
