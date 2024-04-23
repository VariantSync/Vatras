# Indexed Sets of Types

## Module

```agda
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
open import Relation.Binary.PropositionalEquality using (_≗_; subst)
open import Relation.Nullary using (¬_)

open import Function using (id; _∘_; Congruent; Surjective) --IsSurjection)

open Setoid S
private module Eq = IsEquivalence isEquivalence
```

## Definitions

```agda
Index : Set (suc c)
Index = Set c

IndexedSet : Index → Set c
IndexedSet I = I → Carrier

-- an element is within a subset, if there is an index pointing at that element
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
≐→≅ A≐B =
    (λ i → (i ,      A≐B i))
  , (λ i → (i , sym (A≐B i)))

≗→≐ : ∀ {I} {A B : IndexedSet I} → A ≗ B → A ≐ B
≗→≐ A≗B i = Eq.reflexive (A≗B i)

≗→≅ : ∀ {I} {A B : IndexedSet I} → A ≗ B → A ≅ B
≗→≅ A≗B = ≐→≅ (≗→≐ A≗B)
```

## Singletons

```agda
{-|
An indexed set contains only a single element if all indices point to the same element.
-}
Singleton : ∀ {I} → IndexedSet I → Set (c ⊔ ℓ)
Singleton A = ∃[ x ] ∀ i → A i ≈ x

irrelevant-index : ∀ {I} {A : IndexedSet I}
  → Singleton A
  → ∀ {i j} → A i ≈ A j
irrelevant-index (x , Ai≈x) {i} {j} = Eq.trans (Ai≈x i) (Eq.sym (Ai≈x j))
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

## Indexed Sets With Index Translations

```agda
_⊆[_]_ : ∀ {I J} → IndexedSet I → (I → J) → IndexedSet J → Set (c ⊔ ℓ)
_⊆[_]_ {I} A f B = ∀ (i : I) → A i ≈ B (f i)

_≅[_][_]_ : ∀ {I J} → IndexedSet I → (I → J) → (J → I) → IndexedSet J → Set (c ⊔ ℓ)
A ≅[ f ][ f⁻¹ ] B = (A ⊆[ f ] B) × (B ⊆[ f⁻¹ ] A)
```

### Relation to Ordinary Indexed Set Operators

```agda
∈[]→∈ : ∀ {I} {A : IndexedSet I} {a : Carrier} {i : I}
  → a ≈ A i
    ----------
  → a ∈ A
∈[]→∈ {i = i} eq = i , eq

⊆[]→⊆ : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J} {f : I → J}
  → A ⊆[ f ] B
    -----------
  → A ⊆ B
⊆[]→⊆ A⊆[f]B i = ∈[]→∈ (A⊆[f]B i)
-- ⊆[]→⊆ {f = f} A⊆[f]B = λ i → f i , A⊆[f]B i -- equivalent definition

-- verbose name
-- TODO: eta-reducing e here makes Agda have an internal error when importing ⊆[]→⊆.
--       We should isolate that behaviour and report it as a bug.
syntax ⊆[]→⊆ e = ⊆-by-index-translation e

≅[]→≅ : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J} {f   : I → J} {f⁻¹ : J → I}
  → A ≅[ f ][ f⁻¹ ] B
    -----------------
  → A ≅ B
≅[]→≅ (A⊆[f]B , B⊆[f⁻¹]A) = ⊆[]→⊆ A⊆[f]B , ⊆[]→⊆ B⊆[f⁻¹]A

-- verbose name
syntax ≅[]→≅ e = ≅-by-index-translation e

≐→≅[] : ∀ {I} {A B : IndexedSet I} → A ≐ B → A ≅[ id ][ id ] B
≐→≅[] {J} {A} {B} A≐B =
    (λ i →      A≐B i )
  , (λ i → sym (A≐B i))

≗→≅[] : ∀ {I} {A B : IndexedSet I} → A ≗ B → A ≅[ id ][ id ] B
≗→≅[] = ≐→≅[] ∘ ≗→≐

irrelevant-index-⊆ : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J}
  → (x : Carrier)
  → (∀ i → A i ≈ x)
  → (∀ j → B j ≈ x)
    ------------------------
  → ∀ f → A ⊆[ f ] B
irrelevant-index-⊆ _ const-A const-B =
  λ f i →
    Eq.trans (const-A i) (Eq.sym (const-B (f i)))

irrelevant-index-≅ : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J}
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

```agda
⊆[]-refl : ∀ {I} {A : IndexedSet I} → A ⊆[ id ] A
⊆[]-refl = λ _ → Eq.refl

⊆[]-antisym : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J} {f   : I → J} {f⁻¹ : J → I}
  → A ⊆[ f   ] B
  → B ⊆[ f⁻¹ ] A
    -----------------
  → A ≅[ f ][ f⁻¹ ] B
⊆[]-antisym A⊆B B⊆A = A⊆B , B⊆A

⊆[]-trans :
  ∀ {I J K} {A : IndexedSet I} {B : IndexedSet J} {C : IndexedSet K}
    {f : I → J} {g : J → K}
  → A ⊆[ f ] B
  → B ⊆[ g ] C
    --------------
  → A ⊆[ g ∘ f ] C
⊆[]-trans {f = f} A⊆B B⊆C i = Eq.trans (A⊆B i) (B⊆C (f i))

≅[]-refl : ∀ {I} {A : IndexedSet I} → A ≅[ id ][ id ] A
≅[]-refl = ⊆[]-refl , ⊆[]-refl

≅[]-sym : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J} {f : I → J} {f⁻¹ : J → I}
  → A ≅[ f ][ f⁻¹ ] B
    -----------------
  → B ≅[ f⁻¹ ][ f ] A
≅[]-sym (A⊆B , B⊆A) = B⊆A , A⊆B

≅[]-trans :
  ∀ {I J K} {A : IndexedSet I} {B : IndexedSet J} {C : IndexedSet K}
    {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
  → A ≅[ f ][ f⁻¹ ] B
  → B ≅[ g ][ g⁻¹ ] C
    ---------------------------
  → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
≅[]-trans {A = A} {C = C} (A⊆B , B⊆A) (B⊆C , C⊆B) =
  ⊆[]-trans {C = C} A⊆B B⊆C ,
  ⊆[]-trans {C = A} C⊆B B⊆A

⊆→≅ : ∀ {I J} {A : IndexedSet I} {B : IndexedSet J} → (f : I → J) → (f⁻¹ : J → I) → f ∘ f⁻¹ ≗ id → A ⊆[ f ] B → A ≅[ f ][ f⁻¹ ] B
⊆→≅ {A = A} {B = B} f f⁻¹ f∘f⁻¹ A⊆B = A⊆B , (λ i → Eq.sym (subst (λ j → A (f⁻¹ i) ≈ B j) (f∘f⁻¹ i) (A⊆B (f⁻¹ i))))
```

## Equational Reasoning

```agda
module ⊆-Reasoning where
  infix  3 _⊆-∎
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

  _⊆-∎ : ∀ {I} (A : IndexedSet I) → A ⊆ A
  _⊆-∎ _ = ⊆-refl

  syntax step-⊆ A B⊆C A⊆B = A ⊆⟨ A⊆B ⟩ B⊆C

module ≅-Reasoning where
  infix  3 _≅-∎
  infixr 2 _≅⟨⟩_ step-≅-⟨ step-≅-⟩ step-≐-⟨ step-≐-⟩ --step-≅-by-index-translation
  infix  1 ≅-begin_

  ≅-begin_ : ∀{I J} {A : IndexedSet I} {B : IndexedSet J} → A ≅ B → A ≅ B
  ≅-begin_ A≅B = A≅B

  _≅⟨⟩_ : ∀ {I J} (A : IndexedSet I) {B : IndexedSet J} → A ≅ B → A ≅ B
  _ ≅⟨⟩ A≅B = A≅B

  step-≅-⟩ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → A ≅ B
    → A ≅ C
  step-≅-⟩ _ B≅C A≅B = ≅-trans A≅B B≅C

  -- step-≅-by-index-translation : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
  --   → (i→j : I → J)
  --   → (j→i : J → I)
  --   → (∀ (i : I) → A i ≈ B (i→j i))
  --   → (∀ (j : J) → B j ≈ A (j→i j))
  --   → B ≅ C
  --   → A ≅ C
  -- step-≅-by-index-translation _ i→j j→i ti tj B≅C = ≅-trans (⊆-by-index-translation i→j ti , ⊆-by-index-translation j→i tj) B≅C

  step-≅-⟨ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
    → B ≅ C
    → B ≅ A
    → A ≅ C
  step-≅-⟨ A B≅C B≅A = step-≅-⟩ A B≅C (≅-sym B≅A)

  step-≐-⟩ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → A ≐ B
    → A ≅ C
  step-≐-⟩ _ B≅C A≐B = ≅-trans (≐→≅ A≐B) B≅C

  step-≐-⟨ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
    → B ≅ C
    → B ≐ A
    → A ≅ C
  step-≐-⟨ A B≅C B≐A = step-≐-⟩ A B≅C (≐-sym B≐A)

  _≅-∎ : ∀ {I} (A : IndexedSet I) → A ≅ A
  _≅-∎ _ = ≅-refl

  syntax step-≅-⟩ A B≅C A≅B = A ≅⟨ A≅B ⟩ B≅C
  syntax step-≅-⟨ A B≅C B≅A = A ≅⟨ B≅A ⟨ B≅C
  syntax step-≐-⟩ A B≅C (λ i → Ai≈Bi) = A ≐[ i ]⟨ Ai≈Bi ⟩ B≅C
  syntax step-≐-⟨ A B≅C (λ i → Bi≈Ai) = A ≐[ i ]⟨ Bi≈Ai ⟨ B≅C
  -- syntax step-≅-by-index-translation A i→j j→i ti tj B≅C = A ≅[ i→j ]⟨ ti ⟩[ j→i ]⟨ tj ⟩ B≅C

module ≅[]-Reasoning where
  infix  3 _≅[]-∎
  infixr 2 _≅[]⟨⟩_ step-≅[]-⟨ step-≅[]-⟩ step-≐[]-⟨ step-≐[]-⟩
  infix  1 ≅[]-begin_

  ≅[]-begin_ : ∀{I J} {A : IndexedSet I} {B : IndexedSet J} {f : I → J} {g : J → I}
    → A ≅[ f ][ g ] B
    → A ≅[ f ][ g ] B
  ≅[]-begin_ A≅B = A≅B

  _≅[]⟨⟩_ : ∀ {I J} {f : I → J} {g : J → I} (A : IndexedSet I) {B : IndexedSet J}
    → A ≅[ f ][ g ] B
    → A ≅[ f ][ g ] B
  _ ≅[]⟨⟩ A≅B = A≅B

  step-≅[]-⟩ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
               {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
    → B ≅[ g ][ g⁻¹ ] C
    → A ≅[ f ][ f⁻¹ ] B
    → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
  step-≅[]-⟩ _ B≅C A≅B = ≅[]-trans A≅B B≅C

  step-≅[]-⟨ : ∀ {I J K} (A : IndexedSet I) {B : IndexedSet J} {C : IndexedSet K}
                {f : I → J} {f⁻¹ : J → I} {g : J → K} {g⁻¹ : K → J}
    → B ≅[ g ][ g⁻¹ ] C
    → B ≅[ f⁻¹ ][ f ] A
    → A ≅[ g ∘ f ][ f⁻¹ ∘ g⁻¹ ] C
  step-≅[]-⟨ A B≅C B≅A = step-≅[]-⟩ A B≅C (≅[]-sym B≅A)

  step-≐[]-⟩ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
              {g : I → J} {ginv : J → I}
    → B ≅[ g ][ ginv ] C
    → A ≐ B
    → A ≅[ g ][ ginv ] C
  step-≐[]-⟩ _ B≅C A≐B = ≅[]-trans (≐→≅[] A≐B) B≅C

  step-≐[]-⟨ : ∀ {I J} (A {B} : IndexedSet I) {C : IndexedSet J}
                {g : I → J} {ginv : J → I}
    → B ≅[ g ][ ginv ] C
    → B ≐ A
    → A ≅[ g ][ ginv ] C
  step-≐[]-⟨ A B≅C B≐A = step-≐[]-⟩ A B≅C (≐-sym B≐A)

  _≅[]-∎ : ∀ {I} (A : IndexedSet I)
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
  - `Symmetric _≈ᵃ_`: reflexivity over renamed indices is required for a detail in the proof.
  - `Symmetric _≈ᵇ_`: symmetry over original indices is required for a detail in the proof.
```agda
re-indexʳ : ∀ {A B : Index}
    {_≈ᵃ_ : Rel A c} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B c} -- Equality of original indices
  → (rename : A → B)
  → (M : IndexedSet B)
  → Surjective _≈ᵃ_ _≈ᵇ_ rename
  → RB.Reflexive _≈ᵃ_
  → RB.Symmetric _≈ᵇ_
  → Congruent _≈ᵇ_ _≈_ M
    ---------------------
  → M ⊆ (M ∘ rename)
re-indexʳ {A} {B} {_≈ᵃ_} {_≈ᵇ_} rename M rename-is-surjective ≈ᵃ-refl ≈ᵇ-sym M-is-congruent b =
  a , same-picks
  where suitable-a : Σ[ a ∈ A ] ({z : A} → z ≈ᵃ a → rename z ≈ᵇ b)
        suitable-a = rename-is-surjective b

        a : A
        a = proj₁ suitable-a

        same-picks : M b ≈ M (rename a)
        same-picks = M-is-congruent (≈ᵇ-sym (proj₂ suitable-a ≈ᵃ-refl))

re-index : ∀ {A B : Index}
    {_≈ᵃ_ : Rel A c} -- Equality of renamed indices
    {_≈ᵇ_ : Rel B c} -- Equality of original indices
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
