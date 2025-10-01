# Indexed Sets of Types

This module implements indexed sets, a way to express subsets in type theory.
The basic idea is to represent a subset of a type `S : Set` in terms of a function
`f : I → S` from any given type `I` (referred to as the _index set_) to `S`.
The idea is that `f` denotes a subset of `S` in terms of its image $im(f)$.
A detailed explanation can be found in section 4.1 of our paper.

In the following be careful to distinguish the terms _index**ed** set_ and _index set_.

## Module

The target set of an indexed set is given in terms of a setoid
because we need a way to compare elements for equality to determine
where two indices point to the same element (`A(i) ≈ A(j)` for two indices `i j : I`).
```agda
open import Level using (Level)
open import Relation.Binary as RB using (Setoid)

module Vatras.Data.IndexedSet {c ℓ : Level} (S : Setoid c ℓ) where
```

## Imports

```agda
open Level using (0ℓ; suc; _⊔_)

open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≗_; subst)
open RB using (Rel; Setoid; Antisym; IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous using (IREL; Reflexive; Symmetric; Transitive; IsIndexedEquivalence)
open import Relation.Binary.Indexed.Homogeneous using (IsIndexedPartialOrder)
open import Relation.Nullary using (¬_)

open import Function using (id; _∘_; Congruent; Surjective) --IsSurjection)

-- We open the Setoid S so that we can access the target set as 'Carrier' and the equivalence relation as _≈_
open Setoid S
module Eq = IsEquivalence isEquivalence
```

## Definitions

```agda
variable
  iℓ jℓ kℓ : Level

-- An index can just be any set (of any universe, which is why it looks so complicated).
Index : (iℓ : Level) → Set (suc iℓ)
Index iℓ = Set iℓ

-- An indexed set is a function from any given index set to the carrier.
IndexedSet : Index iℓ → Set (c ⊔ iℓ)
IndexedSet I = I → Carrier

{-|
Containment:
An element is within a subset, if there is an index pointing at that element.
-}
_∈_ : ∀ {I : Set iℓ} → Carrier → IndexedSet I → Set (ℓ ⊔ iℓ)
a ∈ A = ∃[ i ] (a ≈ A i)

{-|
Subset:
An indexed set A is a subset of another indexed set B
if all elements A is pointing at are also contained in B.
-}
_⊆_ : IREL (IndexedSet {iℓ}) (IndexedSet {jℓ}) (ℓ ⊔ iℓ ⊔ jℓ)
_⊆_ {i₁ = I} A B = ∀ (i : I) → A i ∈ B

{-|
Equivalence:
Two indexed sets are equivalent if they are subsets of each other.
-}
_≅_ : IREL (IndexedSet {iℓ}) (IndexedSet {jℓ}) (ℓ ⊔ iℓ ⊔ jℓ)
A ≅ B = (A ⊆ B) × (B ⊆ A)

{-|
Pointwise equivalence for indexed sets:
This equivalence is defined over indexed sets with the same index set 'I'.
Two indexed sets are pointwise equal if same indices point to same values.
This definition is the same as _≗_ from the standard-library but generalized to an arbitrary
underlying equivalence relation _≈_.
-}
_≐_ : ∀ {I : Set iℓ} (A B : IndexedSet I) → Set (ℓ ⊔ iℓ)
_≐_ {I = I} A B = ∀ (i : I) → A i ≈ B i

{-|
Pointwise equivalence is a special case of equivalence.
Hence, we can conclude that two sets are equivalent,
if they are pointwise equal.
-}
≐→≅ : ∀ {I : Set iℓ} {A B : IndexedSet I}
  → A ≐ B
    ------
  → A ≅ B
≐→≅ A≐B =
    (λ i → (i ,      A≐B i))
  , (λ i → (i , sym (A≐B i)))

{-|
We can conclude pointwise equality of indexed sets from
pointwise equality of functions.
-}
≗→≐ : ∀ {I : Set iℓ} {A B : IndexedSet I}
  → A ≗ B
    ------
  → A ≐ B
≗→≐ A≗B i = Eq.reflexive (A≗B i)

{-|
We can conclude equality of indexed sets from
pointwise equality of functions.
-}
≗→≅ : ∀ {I : Set iℓ} {A B : IndexedSet I}
  → A ≗ B
    ------
  → A ≅ B
≗→≅ = ≐→≅ ∘ ≗→≐

{-|
Equivalence of indices:
For an indexed set A, two indices i, j are equivalent if
they point to the same element.
-}
_⊢_≡ⁱ_ : ∀ {I : Set iℓ} (A : IndexedSet I) → I → I → Set ℓ
A ⊢ i ≡ⁱ j = A i ≈ A j
```

## Inverse Operations

```agda
_∉_ : ∀ {I : Set iℓ} → Carrier → IndexedSet I → Set (ℓ ⊔ iℓ)
a ∉ A = ∀ i → ¬ (a ≈ A i)
```

## Singletons

```agda
{-|
An indexed set contains only a single element if all indices point to the same element.
-}
Singleton : ∀ {I : Set iℓ} → IndexedSet I → Set (c ⊔ ℓ ⊔ iℓ)
Singleton A = ∃[ x ] ∀ i → A i ≈ x

{-|
Eliminator for singleton sets:
For singleton sets, indices do not matter.
-}
irrelevant-index : ∀ {I : Set iℓ} {A : IndexedSet I}
  → Singleton A
    --------------------
  → ∀ {i j} → A i ≈ A j
irrelevant-index (x , Ai≈x) {i} {j} = Eq.trans (Ai≈x i) (Eq.sym (Ai≈x j))
```

## Properties

We now prove the following theorems:

- Subset `_⊆_` is a partial order.
- Equivalence `_≅_` is an equivalence relation.
- Pointwise equivalence `_≐_` is an equivalence relation.
- Index equivalence `_≡ⁱ_` is an equivalence relation and congruent.

```agda
⊆-refl : Reflexive (IndexedSet {iℓ}) _⊆_
⊆-refl i = i , Eq.refl

-- There is no antisymmetry definition in Relation.Binary.Indexed.Heterogeneous.Definition. Adding that to the standard library would be good and a low hanging fruit.
⊆-antisym : ∀ {I : Set iℓ} {J : Set jℓ} → Antisym (_⊆_ {i₁ = I}) (_⊆_ {i₁ = J}) (_≅_)
⊆-antisym l r = l , r

-- There are no generalized transitivity, symmetry and antisymmetry definitions which allow different levels in Relation.Binary.Indexed.Heterogeneous.Definition . Adding that to the standard library would be good and a low hanging fruit.
⊆-trans : Transitive (IndexedSet {iℓ}) _⊆_
⊆-trans A⊆B B⊆C i =
  -- This proof looks resembles state monad bind >>=.
  -- interesting... 🤔
  let (j , Ai≈Bj) = A⊆B i
      (k , Bj≈Ck) = B⊆C j
   in k , Eq.trans Ai≈Bj Bj≈Ck

≅-refl : Reflexive (IndexedSet {iℓ}) _≅_
≅-refl = ⊆-refl , ⊆-refl

≅-sym : Symmetric (IndexedSet {iℓ}) _≅_
≅-sym (l , r) = r , l

≅-trans : Transitive (IndexedSet {iℓ}) _≅_
≅-trans (A⊆B , B⊆A) (B⊆C , C⊆B) =
    ⊆-trans A⊆B B⊆C
  , ⊆-trans C⊆B B⊆A

≅-IsIndexedEquivalence : IsIndexedEquivalence (IndexedSet {iℓ}) _≅_
≅-IsIndexedEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }

-- There is no heterogeneous version in the standard library. Hence, we only use the homogeneous one here.
⊆-IsIndexedPartialOrder : IsIndexedPartialOrder (IndexedSet {iℓ}) _≅_ _⊆_
⊆-IsIndexedPartialOrder = record
  { isPreorderᵢ = record
    { isEquivalenceᵢ = record
      { reflᵢ = ≅-refl
      ; symᵢ = ≅-sym
      ; transᵢ = ≅-trans
      }
    ; reflexiveᵢ = proj₁
    ; transᵢ = ⊆-trans
    }
  ; antisymᵢ = ⊆-antisym
  }

≐-refl : ∀ {I} → RB.Reflexive (_≐_ {iℓ} {I})
≐-refl i = refl

≐-sym : ∀ {I} → RB.Symmetric (_≐_ {iℓ} {I})
≐-sym x≐y i = sym (x≐y i)

≐-trans : ∀ {I} → RB.Transitive (_≐_ {iℓ} {I})
≐-trans x≐y y≐z i = trans (x≐y i) (y≐z i)

≐-IsEquivalence : ∀ {I} → IsEquivalence (_≐_ {iℓ} {I})
≐-IsEquivalence = record
  { refl = ≐-refl
  ; sym = ≐-sym
  ; trans = ≐-trans
  }

≡ⁱ-IsEquivalence : ∀ {iℓ} {I : Set iℓ} {A : IndexedSet I} → IsEquivalence (A ⊢_≡ⁱ_)
≡ⁱ-IsEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

≡ⁱ-congruent :  ∀ {iℓ} {I : Set iℓ} (A : IndexedSet I) → Congruent (A ⊢_≡ⁱ_) _≈_ A
≡ⁱ-congruent _ proof = proof
```

## Indexed Sets with Index Translations

Above, we defined containment `a ∈ A` such that there just has to be some index `i` pointing to the respective element `A i ≈ a`.
Sometimes it would be useful though if we would know how to obtain this index `i`.
When comparing two indexed sets A and B, instead of assuming there there is just some index `j` in `B` for every index `i` in `A`,
it will prove very useful to instead prove the existence of `i` in terms of an _index translation_ function `f : I → J` such that `A i ≈ B (f i)`.
We hence define a new subset and equivalence relation that remember the index translation, written down in square brackets `[_]`.
For example, `A ⊆[ f ] B` then means that an indexed set `A` is a subset of `B` as proven by the index translation function `f`.

```agda
_⊆[_]_ : ∀ {I : Set iℓ} {J : Set jℓ} → IndexedSet I → (I → J) → IndexedSet J → Set (ℓ ⊔ iℓ)
_⊆[_]_ {I = I} A f B = ∀ (i : I) → A i ≈ B (f i)

_≅[_][_]_ : ∀ {I : Set iℓ} {J : Set jℓ} → IndexedSet I → (I → J) → (J → I) → IndexedSet J → Set (ℓ ⊔ iℓ ⊔ jℓ)
A ≅[ f ][ f⁻¹ ] B = (A ⊆[ f ] B) × (B ⊆[ f⁻¹ ] A)
```

### Relation to Ordinary Indexed Set Operators

Our new relations can be converted back to the old ones by just forgetting the explicit index translations.

```agda
∈[]→∈ : ∀ {I : Set iℓ} {A : IndexedSet I} {a : Carrier} {i : I}
  → a ≈ A i
    ----------
  → a ∈ A
∈[]→∈ {i = i} eq = i , eq

⊆[]→⊆ : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} {f : I → J}
  → A ⊆[ f ] B
    -----------
  → A ⊆ B
⊆[]→⊆ A⊆[f]B i = ∈[]→∈ (A⊆[f]B i)
-- ⊆[]→⊆ {f = f} A⊆[f]B = λ i → f i , A⊆[f]B i -- equivalent definition that might be easier to understand

≅[]→≅ : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} {f : I → J} {f⁻¹ : J → I}
  → A ≅[ f ][ f⁻¹ ] B
    -----------------
  → A ≅ B
≅[]→≅ (A⊆[f]B , B⊆[f⁻¹]A) = ⊆[]→⊆ A⊆[f]B , ⊆[]→⊆ B⊆[f⁻¹]A
```


As Agda implements constructive logic, the converse is also possible.
```agda
∈-index : ∀ {I : Set iℓ} {A : IndexedSet I} {a : Carrier}
  → a ∈ A
  → I
∈-index (i , eq) = i

∈→∈[] : ∀ {I : Set iℓ} {A : IndexedSet I} {a : Carrier}
  → (p : a ∈ A)
    ----------
  → a ≈ A (∈-index p)
∈→∈[] (i , eq) = eq

⊆-index : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → A ⊆ B
  → I → J
⊆-index A⊆B i = ∈-index (A⊆B i)

⊆→⊆[] : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → (subset : A ⊆ B)
    -----------
  → A ⊆[ ⊆-index subset ] B
⊆→⊆[] A⊆B i = proj₂ (A⊆B i)

≅→≅[] : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → (eq : A ≅ B)
    -----------------
  → A ≅[ ⊆-index (proj₁ eq) ][ ⊆-index (proj₂ eq) ] B
≅→≅[] (A⊆B , B⊆A) = (⊆→⊆[] A⊆B) , (⊆→⊆[] B⊆A)
```


If two indexed sets are pointwise equal, they are equivelent in terms of the identify function because
indices do not have to be translated.

```agda
≐→≅[] : ∀ {I : Set iℓ} {A B : IndexedSet I}
  → A ≐ B
    -----------------
  → A ≅[ id ][ id ] B
≐→≅[] {J} {A} {B} A≐B =
    (λ i →      A≐B i )
  , (λ i → sym (A≐B i))

≗→≅[] : ∀ {I : Set iℓ} {A B : IndexedSet I}
  → A ≗ B
    -----------------
  → A ≅[ id ][ id ] B
≗→≅[] = ≐→≅[] ∘ ≗→≐
```

If two indexed sets are singleton sets with the same constant element,
any function can be used to translated indices because indices do not matter at all.

```agda
irrelevant-index-⊆ : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → (x : Carrier)
  → (∀ i → A i ≈ x)
  → (∀ j → B j ≈ x)
    ------------------------
  → ∀ f → A ⊆[ f ] B
irrelevant-index-⊆ _ const-A const-B =
  λ f i →
    Eq.trans (const-A i) (Eq.sym (const-B (f i)))

irrelevant-index-≅ : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → (x : Carrier)
  → (∀ i → A i ≈ x)
  → (∀ j → B j ≈ x)
    ------------------------
  → ∀ f g → A ≅[ f ][ g ] B
irrelevant-index-≅ x const-A const-B =
  λ f g →
      irrelevant-index-⊆ x const-A const-B f
    , irrelevant-index-⊆ x const-B const-A g
```

### Basic Properties

We now prove the following theorems:

- Subset with index translation `_⊆[_]_` is a partial order.
- Equivalence with index translation `_≅[_][_]_` is an equivalence relation.

```agda
⊆[]-refl : ∀ {I : Set iℓ} {A : IndexedSet I} → A ⊆[ id ] A
⊆[]-refl = λ _ → Eq.refl

⊆[]-antisym : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} {f   : I → J} {f⁻¹ : J → I}
  → A ⊆[ f   ] B
  → B ⊆[ f⁻¹ ] A
    -----------------
  → A ≅[ f ][ f⁻¹ ] B
⊆[]-antisym A⊆B B⊆A = A⊆B , B⊆A

⊆[]-trans :
  ∀ {I : Set iℓ} {J : Set jℓ} {K : Set kℓ} {A : IndexedSet I} {B : IndexedSet J} {C : IndexedSet K}
    {f : I → J} {g : J → K}
  → A ⊆[ f ] B
  → B ⊆[ g ] C
    --------------
  → A ⊆[ g ∘ f ] C
⊆[]-trans {f = f} A⊆B B⊆C i = Eq.trans (A⊆B i) (B⊆C (f i))

≅[]-refl : ∀ {I : Set iℓ} {A : IndexedSet I} → A ≅[ id ][ id ] A
≅[]-refl = ⊆[]-refl , ⊆[]-refl

≅[]-sym : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} {f : I → J} {f⁻¹ : J → I}
  → A ≅[ f ][ f⁻¹ ] B
    -----------------
  → B ≅[ f⁻¹ ][ f ] A
≅[]-sym (A⊆B , B⊆A) = B⊆A , A⊆B

≅[]-trans :
  ∀ {I : Set iℓ} {J : Set jℓ} {K : Set kℓ} {A : IndexedSet I} {B : IndexedSet J} {C : IndexedSet K}
    {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
  → A ≅[ f ][ f⁻¹ ] B
  → B ≅[ g ][ g⁻¹ ] C
    ---------------------------
  → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
≅[]-trans {A = A} {C = C} (A⊆B , B⊆A) (B⊆C , C⊆B) =
  ⊆[]-trans {C = C} A⊆B B⊆C ,
  ⊆[]-trans {C = A} C⊆B B⊆A
```

We may conclude equivalence of two indexed sets `A` and `B` if one is a subset of each other
in terms of an index translation `f` and when there exists an inverse function `f⁻¹`.
For the backwards direction, we have to prove that `∀ j: A (f⁻¹ j) ≈ B j`.
By assumption, we already know that `∀ i: A i ≈ B (f i)` because `A ⊆[ f ] B`.
Hence, we also know that `∀ j: A (f⁻¹ j) ≈ B (f (f⁻¹ j))`.
By substitution, we find that the two inverse functions annihilate each other on the right,
leaving us with the statement to prove.

```agda
⊆→≅ : ∀ {I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J}
  → (f : I → J) (f⁻¹ : J → I)
  → f ∘ f⁻¹ ≗ id
  → A ⊆[ f ] B
    -----------------
  → A ≅[ f ][ f⁻¹ ] B
⊆→≅ {A = A} {B = B} f f⁻¹ f∘f⁻¹ A⊆B = A⊆B , (λ j → Eq.sym (subst (λ x → A (f⁻¹ j) ≈ B x) (f∘f⁻¹ j) (A⊆B (f⁻¹ j))))
```

## Equational Reasoning

The following modules define equational reasoning for indexed sets for the relations
`_⊆_`, `_≅_`, and `_≅[_][_]_`.
You an use these reasoning definitions by opening the respective module (e.g., `open ⊆-Reasoning`).

```agda
module ⊆-Reasoning where
  infix  3 _⊆-∎
  infixr 2 _⊆⟨⟩_ step-⊆
  infix  1 ⊆-begin_

  ⊆-begin_ : ∀{I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} → A ⊆ B → A ⊆ B
  ⊆-begin_ A⊆B = A⊆B

  _⊆⟨⟩_ : ∀ {I : Set iℓ} {J : Set jℓ} (A : IndexedSet I) {B : IndexedSet J} → A ⊆ B → A ⊆ B
  _ ⊆⟨⟩ A⊆B = A⊆B

  step-⊆ : ∀ {I J K : Set iℓ} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ⊆ C
    → A ⊆ B
    → A ⊆ C
  step-⊆ _ B⊆C A⊆B = ⊆-trans A⊆B B⊆C

  _⊆-∎ : ∀ {I : Set iℓ} (A : IndexedSet I) → A ⊆ A
  _⊆-∎ _ = ⊆-refl

  syntax step-⊆ A B⊆C A⊆B = A ⊆⟨ A⊆B ⟩ B⊆C

module ≅-Reasoning where
  infix  3 _≅-∎
  infixr 2 _≅⟨⟩_ step-≅-⟨ step-≅-⟩ step-≐-⟨ step-≐-⟩ --step-≅-by-index-translation
  infix  1 ≅-begin_

  ≅-begin_ : ∀{I J : Set iℓ} {A : IndexedSet I} {B : IndexedSet J} → A ≅ B → A ≅ B
  ≅-begin_ A≅B = A≅B

  _≅⟨⟩_ : ∀ {I J : Set iℓ} (A : IndexedSet I) {B : IndexedSet J} → A ≅ B → A ≅ B
  _ ≅⟨⟩ A≅B = A≅B

  step-≅-⟩ : ∀ {I J K : Set iℓ} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → A ≅ B
    → A ≅ C
  step-≅-⟩ _ B≅C A≅B = ≅-trans A≅B B≅C

  step-≅-⟨ : ∀ {I J K : Set iℓ} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → B ≅ A
    → A ≅ C
  step-≅-⟨ A B≅C B≅A = step-≅-⟩ A B≅C (≅-sym B≅A)

  step-≐-⟩ : ∀ {I J : Set iℓ} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → A ≐ B
    → A ≅ C
  step-≐-⟩ _ B≅C A≐B = ≅-trans (≐→≅ A≐B) B≅C

  step-≐-⟨ : ∀ {I J : Set iℓ} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → B ≐ A
    → A ≅ C
  step-≐-⟨ A B≅C B≐A = step-≐-⟩ A B≅C (≐-sym B≐A)

  _≅-∎ : ∀ {I : Set iℓ} (A : IndexedSet I) → A ≅ A
  _≅-∎ _ = ≅-refl

  syntax step-≅-⟩ A B≅C A≅B = A ≅⟨ A≅B ⟩ B≅C
  syntax step-≅-⟨ A B≅C B≅A = A ≅⟨ B≅A ⟨ B≅C
  syntax step-≐-⟩ A B≅C (λ i → Ai≈Bi) = A ≐[ i ]⟨ Ai≈Bi ⟩ B≅C
  syntax step-≐-⟨ A B≅C (λ i → Bi≈Ai) = A ≐[ i ]⟨ Bi≈Ai ⟨ B≅C

module ≅[]-Reasoning where
  infix  3 _≅[]-∎
  infixr 2 _≅[]⟨⟩_ step-≅[]-⟨ step-≅[]-⟩ step-≐[]-⟨ step-≐[]-⟩
  infix  1 ≅[]-begin_

  ≅[]-begin_ : ∀{I : Set iℓ} {J : Set jℓ} {A : IndexedSet I} {B : IndexedSet J} {f : I → J} {g : J → I}
    → A ≅[ f ][ g ] B
    → A ≅[ f ][ g ] B
  ≅[]-begin_ A≅B = A≅B

  _≅[]⟨⟩_ : ∀ {I : Set iℓ} {J : Set jℓ} {f : I → J} {g : J → I} (A : IndexedSet I) {B : IndexedSet J}
    → A ≅[ f ][ g ] B
    → A ≅[ f ][ g ] B
  _ ≅[]⟨⟩ A≅B = A≅B

  step-≅[]-⟩ : ∀ {I : Set iℓ} {J : Set jℓ} {K : Set kℓ} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
               {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
    → B ≅[ g ][ g⁻¹ ] C
    → A ≅[ f ][ f⁻¹ ] B
    → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
  step-≅[]-⟩ _ B≅C A≅B = ≅[]-trans A≅B B≅C

  step-≅[]-⟨ : ∀ {I : Set iℓ} {J : Set jℓ} {K : Set kℓ} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
                {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
    → B ≅[ g ][ g⁻¹ ] C
    → B ≅[ f⁻¹ ][ f ] A
    → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
  step-≅[]-⟨ A B≅C B≅A = step-≅[]-⟩ A B≅C (≅[]-sym B≅A)

  step-≐[]-⟩ : ∀ {I : Set iℓ} {J : Set jℓ} (A {B} : IndexedSet I) {C : IndexedSet J}
              {g : I → J} {ginv : J → I}
    → B ≅[ g ][ ginv ] C
    → A ≐ B
    → A ≅[ g ][ ginv ] C
  step-≐[]-⟩ _ B≅C A≐B = ≅[]-trans (≐→≅[] A≐B) B≅C

  step-≐[]-⟨ : ∀ {I : Set iℓ} {J : Set jℓ} (A {B} : IndexedSet I) {C : IndexedSet J}
                {g : I → J} {ginv : J → I}
    → B ≅[ g ][ ginv ] C
    → B ≐ A
    → A ≅[ g ][ ginv ] C
  step-≐[]-⟨ A B≅C B≐A = step-≐[]-⟩ A B≅C (≐-sym B≐A)

  _≅[]-∎ : ∀ {I : Set iℓ} (A : IndexedSet I)
    → A ≅[ id ][ id ] A
  _≅[]-∎ _ = ≅[]-refl

  syntax step-≅[]-⟩ A B≅C A≅B = A ≅[]⟨ A≅B ⟩ B≅C
  syntax step-≅[]-⟨ A B≅C B≅A = A ≅[]⟨ B≅A ⟨ B≅C
  syntax step-≐[]-⟩ A B≅C (λ i → Ai≈Bi) = A ≐[ i ]⟨ Ai≈Bi ⟩ B≅C
  syntax step-≐[]-⟨ A B≅C (λ i → Bi≈Ai) = A ≐[ i ]⟨ Bi≈Ai ⟨ B≅C
```

## Common sets and relations

```agda
{-|
The empty indexed set.
An indexed set is empty, when there is no index
because then there is no way to point at anything.
-}
𝟘 : IndexedSet {0ℓ} ⊥
𝟘 = λ ()

{-|
A canonical type of singleton indexed sets.
A singleton set has exactly one index because
it can only point at exactly one element.
As a representative set with one element, we use the
canonical '⊤' here.
-}
𝟙 : (iℓ : Level) → Set (c ⊔ iℓ)
𝟙 iℓ = IndexedSet {iℓ} ⊤

{-|
An indexed set is not empty if there exists
at least one index because this index must point
at something.
-}
nonempty : ∀ {I : Set iℓ} → IndexedSet I → Set iℓ
nonempty {I = I} _ = I

{-|
We can retrieve an element from a non-empty indexed set.
This proves that our definition of nonempty indeed
implies that there is an element in each non-empty indexed set.
-}
get-from-nonempty : ∀ {I : Set iℓ}
  → (A : IndexedSet I)
  → nonempty A
    ----------------
  → Carrier
get-from-nonempty A i = A i

-- A predicate that checks whether an indexed set is empty
empty : ∀ {I : Set iℓ} → IndexedSet I → Set iℓ
empty A = ¬ (nonempty A)

-- Proof that the canonical empty indexed set 𝟘 is indeed empty.
𝟘-is-empty : empty 𝟘
𝟘-is-empty ()

-- the empty indexed set is a subset of every indexed set
𝟘⊆A : ∀ {I : Set iℓ} {A : IndexedSet I}
    -----
  → 𝟘 ⊆ A
𝟘⊆A = λ ()

-- every empty indexed set is also a subset of the canonical empty set
empty-set⊆𝟘 : ∀ {I : Set iℓ} {A : IndexedSet I}
  → empty A
    -------
  → A ⊆ 𝟘
empty-set⊆𝟘 A-empty i with A-empty i
...| ()

{-|
The above theorems imply that every empty indexed set
must be equivalent to the canonical empty indexed set 𝟘.
-}
all-empty-sets-are-equal : ∀ {I : Set iℓ} {A : IndexedSet I}
  → empty A
    -------
  → A ≅ 𝟘
all-empty-sets-are-equal A-empty = empty-set⊆𝟘 A-empty , 𝟘⊆A

-- A canonical singleton indexed set is not empty.
singleton-set-is-nonempty : (A : 𝟙 iℓ) → nonempty A
singleton-set-is-nonempty _ = tt
```

## Further Properties

### Reindexing

We can rename the indices of a multiset M to obtain a subset of M.
```agda

re-indexˡ : ∀ {A B : Set iℓ}
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
  - `Symmetric _≈ᵃ_`: reflexivity over renamed indices is required for a detail in the proof.
  - `Symmetric _≈ᵇ_`: symmetry over original indices is required for a detail in the proof.
```agda
re-indexʳ : ∀ {ℓᵃ ℓᵇ : Level} {A B : Index iℓ}
    {_≈ᵃ_ : Rel A ℓᵃ} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B ℓᵇ} -- Equality of original indices
  → (rename : A → B)
  → (M : IndexedSet B)
  → Surjective _≈ᵃ_ _≈ᵇ_ rename
  → RB.Reflexive _≈ᵃ_
  → RB.Symmetric _≈ᵇ_
  → Congruent _≈ᵇ_ _≈_ M
    ---------------------
  → M ⊆ (M ∘ rename)
re-indexʳ {A = A} {B} {_≈ᵃ_} {_≈ᵇ_} rename M rename-is-surjective ≈ᵃ-refl ≈ᵇ-sym M-is-congruent b =
  a , same-picks
  where suitable-a : Σ[ a ∈ A ] ({z : A} → z ≈ᵃ a → rename z ≈ᵇ b)
        suitable-a = rename-is-surjective b

        a : A
        a = proj₁ suitable-a

        same-picks : M b ≈ M (rename a)
        same-picks = M-is-congruent (≈ᵇ-sym (proj₂ suitable-a ≈ᵃ-refl))

re-index : ∀ {ℓᵃ ℓᵇ : Level} {A B : Index iℓ}
    {_≈ᵃ_ : Rel A ℓᵃ} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B ℓᵇ} -- Equality of original indices
  → (rename : A → B)
  → (M : IndexedSet B)
  → Surjective _≈ᵃ_ _≈ᵇ_ rename
  → RB.Reflexive _≈ᵃ_
  → RB.Symmetric _≈ᵇ_
  → Congruent _≈ᵇ_ _≈_ M
    ---------------------------
  → (M ∘ rename) ≅ M
re-index {_≈ᵃ_ = _≈ᵃ_} rename M rename-is-surjective ≈ᵃ-refl ≈ᵇ-sym M-is-congruent =
    re-indexˡ rename M
  , re-indexʳ {_≈ᵃ_ = _≈ᵃ_} rename M rename-is-surjective ≈ᵃ-refl ≈ᵇ-sym M-is-congruent
```

