# Indexed Sets of Types

## Module

```agda
{-# OPTIONS --allow-unsolved-metas #-}

open import Level using (Level; suc; _⊔_)
open import Relation.Binary as RB using (
  Rel;
  Setoid;
  Antisym;
  IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous using (
  IRel;
  Reflexive;
  Symmetric;
  Transitive;
  IsIndexedEquivalence)
module Data.IndexedSet
  {c ℓ : Level}
  (S : Setoid c ℓ)
  where
```

## Imports

```agda
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Function using (_∘_; Congruent; Surjective) --IsSurjection)

open Setoid S
module Eq = IsEquivalence isEquivalence
```

## Definitions

```agda
Index : Set (suc c)
Index = Set c

IndexedSet : Index → Set c
IndexedSet I = I → Carrier

-- an element is within a subset, if there is an index pointing at that element
-- Later we could employ setoids to parameterize our set formulation in the equivalence relation instead of always relying on propositional equality.
_∈_ : ∀ {I} → Carrier → IndexedSet I → Set (c ⊔ ℓ)
a ∈ A = ∃[ i ] (a ≈ A i)

-- morphisms
-- _⊆_ : ∀ {I J} → IndexedSet I → IndexedSet J → Set ℓ
_⊆_ : IRel IndexedSet (c ⊔ ℓ)
_⊆_ {I} A B = ∀ (i : I) → A i ∈ B

_≅_ : IRel IndexedSet (c ⊔ ℓ)
A ≅ B = (A ⊆ B) × (B ⊆ A)

-- Same indices point to same values.
-- This definition is the same as _≗_ from the standard-library but generalized to an arbitrary
-- underlying equivalence relation _≈_.
_≐_ : ∀ {I} (A B : IndexedSet I) → Set (c ⊔ ℓ)
_≐_ {I} A B = ∀ (i : I) → A i ≈ B i

≐→≅ : ∀ {I} {A B : IndexedSet I} → A ≐ B → A ≅ B -- this acts as cong, too
≐→≅ {J} {A} {B} A≐B =
    (λ i → (i ,      A≐B i))
  , (λ i → (i , sym (A≐B i)))
```

## Properties

```agda
⊆-refl : Reflexive IndexedSet _⊆_
⊆-refl i = i , Eq.refl

-- Todo: There is no antsymmetry definition in Relation.Binary.Indexed.Heterogeneous.Definition. Adding that to the standard library would be good and a low hanging fruit.
⊆-antisym : ∀ {I J} → Antisym (_⊆_ {I} {J}) (_⊆_ {J} {I}) (_≅_ {I} {J})
⊆-antisym l r = l , r

⊆-trans : Transitive IndexedSet _⊆_
⊆-trans A⊆B B⊆C i =
  -- This proof looks resembles state monad bind >>=.
  -- interesting... :thinking_face:
  let (j , Ai≈Bj) = A⊆B i
      (k , Bj≈Ck) = B⊆C j
   in k , Eq.trans Ai≈Bj Bj≈Ck

≅-refl : Reflexive IndexedSet _≅_
≅-refl = ⊆-refl , ⊆-refl

≅-sym : Symmetric IndexedSet _≅_
≅-sym (l , r) = r , l

≅-trans : Transitive IndexedSet _≅_
≅-trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
    ⊆-trans A⊆B B⊆C
  , ⊆-trans C⊆B B⊆A

≅-IsIndexedEquivalence : IsIndexedEquivalence IndexedSet _≅_
≅-IsIndexedEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }

≐-refl : ∀ {I} → RB.Reflexive (_≐_ {I})
≐-refl i = refl

≐-sym : ∀ {I} → RB.Symmetric (_≐_ {I})
≐-sym x≐y i = sym (x≐y i)

≐-trans : ∀ {I} → RB.Transitive (_≐_ {I})
≐-trans x≐y y≐z i = trans (x≐y i) (y≐z i)

≐-IsEquivalence : ∀ {I} → IsEquivalence (_≐_ {I})
≐-IsEquivalence = record
  { refl = ≐-refl
  ; sym = ≐-sym
  ; trans = ≐-trans
  }
```

### Helper Functions for Proving Subset

```agda
⊆-by-index-translation : {I J : Set c} {A : IndexedSet I} {B : IndexedSet J}
  → (t : I → J)
  → (∀ (i : I) → A i ≈ B (t i))
    ---------------------------
  → A ⊆ B
⊆-by-index-translation t t-preserves i = t i , t-preserves i
```

## Equational Reasoning

```agda
module ⊆-Reasoning where
  infix  3 _∎-⊆
  infixr 2 _⊆⟨⟩_ step-⊆
  infix  1 ⊆-begin_

  ⊆-begin_ : ∀{I J} {A : IndexedSet I} {B : IndexedSet J} → A ⊆ B → A ⊆ B
  ⊆-begin_ A⊆B = A⊆B

  _⊆⟨⟩_ : ∀ {I J} (A : IndexedSet I) {B : IndexedSet J} → A ⊆ B → A ⊆ B
  _ ⊆⟨⟩ A⊆B = A⊆B

  step-⊆ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ⊆ C
    → A ⊆ B
    → A ⊆ C
  step-⊆ _ B⊆C A⊆B = ⊆-trans A⊆B B⊆C

  _∎-⊆ : ∀ {I} (A : IndexedSet I) → A ⊆ A
  _∎-⊆ _ = ⊆-refl

  syntax step-⊆ A B⊆C A⊆B = A ⊆⟨ A⊆B ⟩ B⊆C

module ≅-Reasoning where
  infix  3 _∎-≅
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘ step-≐ step-≐˘
  infix  1 ≅-begin_

  ≅-begin_ : ∀{I J} {A : IndexedSet I} {B : IndexedSet J} → A ≅ B → A ≅ B
  ≅-begin_ A⊆B = A⊆B

  _≅⟨⟩_ : ∀ {I J} (A : IndexedSet I) {B : IndexedSet J} → A ≅ B → A ≅ B
  _ ≅⟨⟩ A≅B = A≅B

  step-≅ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → A ≅ B
    → A ≅ C
  step-≅ _ B≅C A≅B = ≅-trans A≅B B≅C

  step-≅˘ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → B ≅ A
    → A ≅ C
  step-≅˘ A B≅C B≅A = step-≅ A B≅C (≅-sym B≅A)

  step-≐ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → A ≐ B
    → A ≅ C
  step-≐ _ B≅C A≐B = ≅-trans (≐→≅ A≐B) B≅C

  step-≐˘ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → B ≐ A
    → A ≅ C
  step-≐˘ A B≅C B≐A = step-≐ A B≅C (≐-sym B≐A)

  _∎-≅ : ∀ {I} (A : IndexedSet I) → A ≅ A
  _∎-≅ _ = ≅-refl

  syntax step-≅ A B≅C A≅B = A ≅⟨ A≅B ⟩ B≅C
  syntax step-≅˘ A B≅C B≅A = A ≅˘⟨ B≅A ⟩ B≅C
  syntax step-≐ A B≅C A≐B = A ≐⟨ A≐B ⟩ B≅C
  syntax step-≐˘ A B≅C B≐A = A ≐˘⟨ B≐A ⟩ B≅C
```

## Common sets and relations

```agda
{-|
The empty set
-}
𝟘 : IndexedSet ⊥
𝟘 = λ ()

{-|
The type of singleton sets over a source.
-}
𝟙 : Set c
𝟙 = IndexedSet ⊤

-- predicate that checks whether a subset is nonempty
-- A set is non-empty when there exists at least one index.
nonempty : ∀ {I} → IndexedSet I → Set c
nonempty {I = I} _ = I --∃[ a ] (a ∈ A)

-- We can retrieve an element from a non-empty set.
-- This proves that our definition of nonempty indeed
-- implies that there is an element in each non-empty set.
get-from-nonempty : ∀ {I}
  → (A : IndexedSet I)
  → nonempty A
    ----------------
  → Carrier
get-from-nonempty A i = A i

-- predicate that checks whether a subset is empty
empty : ∀ {I} → IndexedSet I → Set c
empty A = ¬ (nonempty A)

𝟘-is-empty : empty 𝟘
𝟘-is-empty ()

𝟘⊆A : ∀ {I} {A : IndexedSet I}
    -----
  → 𝟘 ⊆ A
𝟘⊆A = λ ()

empty-set⊆𝟘 : ∀ {I} {A : IndexedSet I}
  → empty A
    -------
  → A ⊆ 𝟘
empty-set⊆𝟘 A-empty i with A-empty i
...| ()

all-empty-sets-are-equal : ∀ {I} {A : IndexedSet I}
  → empty A
    -------
  → A ≅ 𝟘
all-empty-sets-are-equal A-empty = empty-set⊆𝟘 A-empty , 𝟘⊆A

singleton-set-is-nonempty : (A : 𝟙) → nonempty A
singleton-set-is-nonempty _ = tt
```

## Further Properties

### Reindexing

We can rename the indices of a multiset M to obtain a subset of M.
```agda

re-indexˡ : ∀ {A B : Set c}
  → (rename : A → B)
  → (M : IndexedSet B)
    ---------------------
  → (M ∘ rename) ⊆ M
re-indexˡ rename _ a = rename a , Eq.refl
```

If the renaming renames every index (i.e., the renaming is surjective), the
renamed multiset is isomorphic to the original set M.
Surjectivity can be given over any two equality relations `_≈ᵃ_` (equality of renamed indices) and `_≈ᵇ_` (equality of original indices).
We do not require that both relations are indeed equivalence relations but only list those properties we actually need:
  - All indices are renamed. This means that the renaming has to be surjective with respect to
    - equivalence of renamed indices `_≈ᵃ_`
    - equivalence of original indices `_≈ᵇ_`
  - Equal original indices index equal source elements. This means that the equality of original indices `_≈ᵇ_` has to be congruent with
    respect to equivalence `_≈_` of the source elements.
  - `Symmetric _≈ᵇ_`: symmetry over original indices is required for a detail in the proof.
```agda
re-indexʳ : ∀ {A B : Index}
    {_≈ᵃ_ : Rel A c} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B c} -- Equality of original indices
  → (rename : A → B)
  → (M : IndexedSet B)
  → Surjective _≈ᵃ_ _≈ᵇ_ rename
  → RB.Symmetric _≈ᵇ_
  → Congruent _≈ᵇ_ _≈_ M
    ---------------------
  → M ⊆ (M ∘ rename)
re-indexʳ {A} {B} {_} {_≈ᵇ_} rename M rename-is-surjective ≈ᵇ-sym M-is-congruent b =
  a , same-picks
  where suitable-a : Σ[ a ∈ A ] (rename a ≈ᵇ b)
        suitable-a = rename-is-surjective b

        a : A
        a = proj₁ suitable-a

        same-picks : M b ≈ M (rename a)
        same-picks = M-is-congruent (≈ᵇ-sym (proj₂ suitable-a))

re-index : ∀ {A B : Index}
    {_≈ᵃ_ : Rel A c} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B c} -- Equality of original indices
  → (rename : A → B)
  → (M : IndexedSet B)
  → Surjective _≈ᵃ_ _≈ᵇ_ rename
  → RB.Symmetric _≈ᵇ_
  → Congruent _≈ᵇ_ _≈_ M
    ---------------------------
  → (M ∘ rename) ≅ M
re-index {_≈ᵃ_ = _≈ᵃ_} rename M rename-is-surjective ≈ᵇ-sym M-is-congruent =
    re-indexˡ rename M
  , re-indexʳ {_≈ᵃ_ = _≈ᵃ_} rename M rename-is-surjective ≈ᵇ-sym M-is-congruent
```

## Examples

```
-- module Examples where
--   open import Data.Nat using (ℕ)
--   open import Data.Fin using (Fin; suc; zero)
--   open import Relation.Binary.PropositionalEquality as Peq
--   open Level using (0ℓ)

--   ex12 : IndexedSet ℕ Peq.isEquivalence (Fin 2)
--   ex12 zero = 1
--   ex12 (suc zero) = 2

--   ex21 : IndexedSet (Fin 2) ℕ
--   ex21 zero = 2
--   ex21 (suc zero) = 1

--   12≅21 : ex12 ≅ ex21
--   proj₁ 12≅21 zero = suc zero , Eq.refl
--   proj₁ 12≅21 (suc zero) = zero , Eq.refl
--   proj₂ 12≅21 zero = suc zero , Eq.refl
--   proj₂ 12≅21 (suc zero) = zero , Eq.refl

--   -- When the source is smaller than the index, then we have a multi set.
--   exshrink : IndexedSet (Fin 2) ⊤
--   exshrink x = tt
```
