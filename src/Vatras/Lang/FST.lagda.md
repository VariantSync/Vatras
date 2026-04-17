This module formalizes feature structure trees.
We formalize the language, its semantics, and the typing to disallow duplicate neighbors.

```agda
open import Vatras.Framework.Definitions

module Vatras.Lang.FST (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; foldl; foldr; map; filterᵇ; concat; reverse)
open import Data.List.Properties as List using (++-identityˡ; ++-identityʳ)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Relation.Unary.All as All using (All; []; _∷_) renaming (map to map-all)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Product using (Σ; ∃-syntax; ∄-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Size using (Size; ↑_; ∞)

open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary using (Decidable; DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Vatras.Framework.Variants using (Rose; _-<_>-; rose-leaf)
open import Vatras.Framework.Composition.FeatureAlgebra
open import Vatras.Framework.VariabilityLanguage

open import Vatras.Util.Function using (cong-app₂)
```

## Basic Definitions

We configure feature structure trees by choosing which features to include or exclude.
```
Configuration : ℂ
Configuration = F → Bool
```

A single feature structure tree is just a rose tree (which is composed into other rose trees).
```agda
FST : Size → 𝔼
FST i = Rose i

module Impose (AtomSet : 𝔸) where
  FSTA : Size → Set₁
  FSTA i = FST i AtomSet

  private
    A = atoms AtomSet
    _≟_ = atomsEqual? AtomSet

  fst-leaf : A → FSTA ∞
  fst-leaf = rose-leaf
```

We now define an equality relation that determines when to FST nodes should be composed:
Exactly if their atoms are equal.
We also prove that this relation is an equivalence relation.
```agda
  {-|
  Composition equality.
  -}
  infix 15 _≈_
  _≈_ : ∀ {i} → Rel (FSTA i) 0ℓ
  (a -< _ >-) ≈ (b -< _ >-) = a ≡ b

  ≈-refl : ∀ {i} → {a : FSTA i} → a ≈ a
  ≈-refl {.(↑ _)} {_ -< _ >- } = refl

  ≈-reflexive : ∀ {i} → {a b : FSTA i} → a ≡ b → a ≈ b
  ≈-reflexive {.(↑ _)} {_ -< _ >- } refl = refl

  ≈-sym : ∀ {i} → {a b : FSTA i} → a ≈ b → b ≈ a
  ≈-sym {i} {(a -< _ >-)} {(.a -< _ >-)} refl = refl

  ≈-trans : ∀ {i} → {a b c : FSTA i} → a ≈ b → b ≈ c → a ≈ c
  ≈-trans {i} {(a -< _ >-)} {(.a -< _ >-)} {(.a -< _ >-)} refl refl = refl

  {-|
  Composition equality _≈_ is decidable.
  -}
  _==_ : ∀ {i} → Decidable (_≈_ {i})
  (a -< _ >-) == (b -< _ >-) = a ≟ b
```

Conversely, we can also state when two FSTs should not be composed.
```agda
  infix 15 _≉_
  _≉_ : ∀ {i} → Rel (FSTA i) 0ℓ
  a ≉ b = ¬ (a ≈ b)

  ≉-sym : ∀ {i} → {a b : FSTA i} → a ≉ b → b ≉ a
  ≉-sym a≉b b≈a = a≉b (≈-sym b≈a)

  ≉-ignores-children : ∀ {i} → {a₁ a₂ b₁ b₂ : FSTA i}
    → a₁ ≈ a₂
    → b₁ ≈ b₂
    → a₁ ≉ b₁
      -------
    → a₂ ≉ b₂
  ≉-ignores-children a₁≈a₂ b₁≈b₂ a₁≉b₁ a₂≈b₂ = a₁≉b₁ (≈-trans a₁≈a₂ (≈-trans a₂≈b₂ (≈-sym b₁≈b₂)))
```

We now introduce some relations to determine whether there is a composition target
for a given feature structure tree in a list of other feature structure tree.

```
  {-|
  t ∈ ts
  if
  the list of feature structure trees ts contains at least one
  tree which has the same root as the tree t.
  TODO: Use standard library üredicates for list containment.
  -}
  infix 15 _∈_
  _∈_ : ∀ {i} → FSTA i → List (FSTA i) → Set₁
  x ∈ xs = Any (x ≈_) xs

  infix 15 _∉_
  _∉_ : ∀ {i} → FSTA i → List (FSTA i) → Set₁
  x ∉ xs = All (x ≉_) xs

  {-|
  xs ⊑ ys iff all elements in xs occur (somewhere) in ys.
  -}
  _⊑_ : ∀ {i} → (xs ys : List (FSTA i)) → Set₁ --\squb=
  xs ⊑ ys = All (_∈ ys) xs

  _⋢_ : ∀ {i} → (xs ys : List (FSTA i)) → Set₁ --\squb=n
  xs ⋢ ys = Any (_∉ ys) xs

  {-|
  Two lists of FSTs are considered disjoint of none of the trees
  in the first list can be composed into an FST in the second list.
  -}
  Disjoint : ∀ {i} → (xs ys : List (FSTA i)) → Set₁
  Disjoint xs ys = All (_∉ ys) xs
```

## Properties

We now prove some useful properties of the above statements.

```agda
  {-|
  There is only one proof for x ∉ ys.
  -}
  ∉-deterministic : ∀ {x : FSTA ∞} (ys : List (FSTA ∞))
    → (p₁ : x ∉ ys)
    → (p₂ : x ∉ ys)
      -------------
    → p₁ ≡ p₂
  ∉-deterministic [] [] [] = refl
  ∉-deterministic {x} (y ∷ ys) (x≉y₁ ∷ pa) (x≉y₂ ∷ pb)
    rewrite ∉-deterministic ys pa pb
    = refl

  {-|
  We can substitute the list of children in an FST while preserving
  inequality because inequality only cares about the atom.
  -}
  map-≉ : ∀ {i} {b xs} (ys : List (FSTA i)) (z : FSTA (↑ i))
    → b -< xs >- ≉ z
    → b -< ys >- ≉ z
  map-≉ ys (z -< zs >-) z≉z refl = z≉z refl

  map-∉ : ∀ {i} {b : A} {cs cs' : List (FSTA i)} {xs : List (FSTA (↑ i))}
    → b -< cs  >- ∉ xs
    → b -< cs' >- ∉ xs
  map-∉ [] = []
  map-∉ {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-≉ cs' x px ∷ map-∉ pxs

  disjoint-[]ˡ : ∀ {i} (xs : List (FSTA i)) → Disjoint [] xs
  disjoint-[]ˡ _ = []

  disjoint-[]ʳ : ∀ {i} (xs : List (FSTA i)) → Disjoint xs []
  disjoint-[]ʳ [] = []
  disjoint-[]ʳ (x ∷ xs) = [] ∷ (disjoint-[]ʳ xs)

  disjoint-grow : ∀ {i} (r : FSTA i) (rs ls : List (FSTA i))
    → Disjoint ls rs
    → r ∉ ls
      --------------------
    → Disjoint ls (r ∷ rs)
  disjoint-grow r rs [] _ _ = []
  disjoint-grow r rs (l ∷ ls) (l∉rs ∷ d-ls-rs) (r≉l ∷ r∉ls)
    = (≉-sym r≉l ∷ l∉rs) ∷ disjoint-grow r rs ls d-ls-rs r∉ls

  disjoint-shiftʳ : ∀ {i} (r : FSTA i) (rs ls : List (FSTA i))
    → Disjoint ls (r ∷ rs)
      --------------------------
    → Disjoint ls (rs ++ r ∷ [])
  disjoint-shiftʳ r rs [] x = []
  disjoint-shiftʳ r rs (l ∷ ls) ((l≉r ∷ l∉rs) ∷ d-ls-rrs)
    = step l r rs l≉r l∉rs ∷ disjoint-shiftʳ r rs ls d-ls-rrs
    where
      step : ∀ {i} (x y : FSTA i) (zs : List (FSTA i))
        → x ≉ y
        → x ∉ zs
        → x ∉ (zs ++ y ∷ [])
      step x y [] x≉y _ = x≉y ∷ []
      step x y (z ∷ zs) x≉y (x≉z ∷ x∉zs) = x≉z ∷ step x y zs x≉y x∉zs
```

## Smart Constructors

```agda
  -- the syntax used in the original paper for paths
  infixr 5 _．_
  _．_ : A → (cs : List (FSTA ∞)) → List (FSTA ∞)
  a ． cs = a -< cs >- ∷ []

  -- helper function when branching in paths
  branches : List (List (FSTA ∞)) → List (FSTA ∞)
  branches = concat
```

## Composition

```agda
  mutual
    infixr 5 _⊕_
    {-|
    Composition of lists of feature structure trees.
    -}
    _⊕_ : ∀ {i} → List (FSTA i) → List (FSTA i) → List (FSTA i)
    l ⊕ r = foldl _⊙_ l r

    {-|
    The following is the definition of ⊕ as written in the paper.
    In fact, this definition is just a foldl, which we hid in the paper
    for easier reading.
    For our definition and proofs, we use the foldl formulation (see above)
    and prove that both definitions are equivalent (below).
    TODO: slightly inconsistent with paper, adapt the paper for conditional-accept revision
    -}
    _⊕'_ : ∀ {i} → List (FSTA i) → List (FSTA i) → List (FSTA i)
    l ⊕' [] = l
    l ⊕' (r ∷ rs) = (l ⊙ r) ⊕' rs

    ⊕≗⊕' : ∀ xs ys → xs ⊕ ys ≡ xs ⊕' ys
    ⊕≗⊕' xs [] = refl
    ⊕≗⊕' xs (y ∷ ys) =
        xs ⊕ (y ∷ ys)
      ≡⟨⟩
        (xs ⊙ y) ⊕ ys
      ≡⟨ ⊕≗⊕' (xs ⊙ y) ys ⟩
        (xs ⊙ y) ⊕' (ys)
      ≡⟨⟩
        xs ⊕' (y ∷ ys)
      ∎


    {-|
    Composition of an FST into a list of FSTs.
    -}
    infixl 5 _⊙_
    _⊙_ : ∀ {i} → List (FSTA i) → FSTA i → List (FSTA i)
    [] ⊙ r = r ∷ []
    (h ∷ t) ⊙ r with r == h
    ... | no _ = h ∷ (t ⊙ r)
    (a -< ca >- ∷ t) ⊙ .a -< cb >- | yes refl = a -< ca ⊕ cb >- ∷ t

  {-|
  A list of FSTs is considered unique if the FSTs are pairwise different regarding composition equality.
  This basically encodes the restriction that FSTs cannot have neighbors with equal atoms.
  To ensure this property recursively, we introduce two further definitions below.
  -}
  Unique : ∀ {i} → List (FSTA i) → Set₁
  Unique = AllPairs _≉_

  mutual
    {-|
    An FST is considered well-formed if its children list is well-formed.
    -}
    WellFormed : ∀ {i} → FSTA i → Set₁
    WellFormed (_ -< cs >-) = AllWellFormed cs

    {-|
    A list of FSTs is well-formed if
    - there are no duplicate atoms at the roots of the FSTs in the list,
    - and all FSTs are well-formed.
    -}
    AllWellFormed : ∀ {i} → List (FSTA i) → Set₁
    AllWellFormed cs = Unique cs × All WellFormed cs

  mutual
    {-|
    Composition _⊕_ preserves well-formedness.
    -}
    ⊕-wf : ∀ {i} {ls rs : List (FSTA i)}
      → AllWellFormed ls
      → AllWellFormed rs
        -----------------------
      → AllWellFormed (ls ⊕ rs)
    ⊕-wf ls-wf ([] , []) = ls-wf
    ⊕-wf ls-wf (_ ∷ u-rs , du-r ∷ du-rs) = ⊕-wf (⊙-wf ls-wf du-r) (u-rs , du-rs)

    {-|
    Composition _⊙_ preserves well-formedness.
    -}
    ⊙-wf : ∀ {i} {l : List (FSTA i)} {r : FSTA i}
      → AllWellFormed l
      → WellFormed r
        ---------------------
      → AllWellFormed (l ⊙ r)
    ⊙-wf ([] , []) du-r = [] ∷ [] , du-r ∷ []
    ⊙-wf {_} {h ∷ _} {r} (_ ∷ _ , _ ∷ _) _ with r == h
    ⊙-wf {_} {(a -< ca >-) ∷ t} {.a -< cb >- } (  _ ∷ _   , wf-ca ∷    _) wf-cb | yes refl with ⊕-wf wf-ca wf-cb
    ⊙-wf                                       (u-h ∷ u-t ,     _ ∷ du-t) _     | yes refl | wf-ca⊕cb
      = (map-∉ u-h) ∷ u-t , wf-ca⊕cb ∷ du-t
    ⊙-wf {_} {a -< ca >- ∷ t} {b -< cb >- } (u-h ∷ u-t , du-h ∷ du-t) du-r | no _ with ⊙-wf (u-t , du-t) du-r
    ⊙-wf {_} {a -< ca >- ∷ t} {b -< cb >- } (u-h ∷ u-t , du-h ∷ du-t) du-r | no a≢b | u-rec , du-rec
      = ind a≢b u-h ∷ u-rec , du-h ∷ du-rec
      where
        ind :  ∀ {i} {a b} {ca cb : List (FSTA i)} {t : List (FSTA (↑ i))}
          → ¬ (a ≡ b)
          → b -< cb >- ∉ t
          → b -< cb >- ∉ (t ⊙ (a -< ca >-))
        ind {t = []} a≢b b∉t = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ []
        ind {_} {a} {_} {ca} {_}  {t ∷ ts} a≢b b∉t with (a -< ca >-) == t
        ind {_} {a} {_} {ca} {cb} {(.a -< ct >-) ∷ ts} a≢b (  _ ∷ b∉ts) | yes refl = (λ b≡a → a≢b (Eq.sym b≡a)) ∷ b∉ts
        ind {_} {a} {_} {ca} {cb} {( t -< ct >-) ∷ ts} a≢b (b≢t ∷ b∉ts) | no   a≢t = b≢t ∷ (ind a≢b b∉ts)

  mutual
    {-|
    There is only one proof of WellFormed x.
    -}
    WellFormed-deterministic : ∀ {x : FSTA ∞}
      → (a : WellFormed x)
      → (b : WellFormed x)
        ------------------
      → a ≡ b
    WellFormed-deterministic {_ -< cs >- } a b = AllWellFormed-deterministic cs a b

    {-|
    There is only one proof of AllWellFormed xs.
    -}
    AllWellFormed-deterministic : ∀ (xs : List (FSTA ∞))
      → (ua : AllWellFormed xs)
      → (ub : AllWellFormed xs)
        -----------------------
      → ua ≡ ub
    AllWellFormed-deterministic [] ([] , []) ([] , []) = refl
    AllWellFormed-deterministic (x ∷ xs) (a-x∉xs ∷ a-u-xs , a-ur-x ∷ a-ur-xs) (b-x∉xs ∷ b-u-xs , b-ur-x ∷ b-ur-xs)
      with AllWellFormed-deterministic xs (a-u-xs , a-ur-xs) (b-u-xs , b-ur-xs)
    ... | eq
      rewrite (Eq.cong proj₁ eq)
      rewrite (Eq.cong proj₂ eq)
      rewrite WellFormed-deterministic a-ur-x b-ur-x
      rewrite ∉-deterministic xs a-x∉xs b-x∉xs
      = refl

  {-|
  If an FST l with no composition target in rs is composed into rs,
  the l will just be appended at the end of the list.
  -}
  ⊙-stranger : ∀ {i} (l : FSTA i) (rs : List (FSTA i))
    → l ∉ rs
      ----------------
    → rs ⊙ l ≡ rs ∷ʳ l
  ⊙-stranger l [] _ = refl
  ⊙-stranger l (r ∷ rs) (l≢r ∷ l∉rs) with l == r -- TODO: Is there an easier way to tell Agda that we already know l ≢ r?
  ... | yes l≡r = ⊥-elim (l≢r l≡r)
  ... | no  _   = Eq.cong (r ∷_) (⊙-stranger l rs l∉rs)

  {-|
  Composing disjoint lists of feature structure trees will just append on to the other,
  assuming that the right list is unique to avoid self-composition.
  -}
  ⊕-strangers : ∀ {i} (ls rs : List (FSTA i))
    → Unique rs
    → Disjoint rs ls
      ------------------
    → ls ⊕ rs ≡ ls ++ rs
  ⊕-strangers ls [] _ _ rewrite ++-identityʳ ls = refl
  ⊕-strangers ls (r ∷ rs) (r∉rs ∷ u-rs) (r∉ls ∷ d-ls-rs)
    -- Goal: (ls ⊙ r) ⊕ rs ≡ ls ++ r ∷ rs
    rewrite (Eq.sym (List.∷ʳ-++ ls r rs))
    -- Goal: (ls ⊙ r) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    rewrite ⊙-stranger r ls r∉ls
    -- Goal: (ls ++ r ∷ []) ⊕ rs ≡ (ls ++ r ∷ []) ++ rs
    = ⊕-strangers (ls ++ r ∷ []) rs u-rs (disjoint-shiftʳ r ls rs (disjoint-grow r ls rs d-ls-rs r∉rs))

  ⊕-idˡ :
    ∀ {i} (rs : List (FSTA i))
    → Unique rs
      -------------
    → [] ⊕ rs ≡ rs
  ⊕-idˡ rs u-rs = ⊕-strangers [] rs u-rs (disjoint-[]ʳ rs)

  {-|
  A Feature Structure Forest (FSF) consists
  of a well-formed list of FSTs.
  Each FSF will represent one feature in
  a product line.
  -}
  record FSF : Set₁ where
    constructor _⊚_
    field
      trees : List (FSTA ∞)
      valid : AllWellFormed trees
  open FSF public

  forget-uniqueness : FSF → List (FSTA ∞)
  forget-uniqueness = trees

  {-|
  A feature is a named feature structure forest.
  All features in a product line are required to have
  the very same root node, otherwise they could not be
  imposed.
  To ensure this constraint by design, this root node is
  part of the SPL definition and not the features.
  Hence, a feature is a rootless tree: It holds a list of trees,
  which denote the children of the common root.
  -}
  infixr 3 _::_
  record Feature : Set₁ where
    constructor _::_
    field
      name : F
      impl : FSF
  open Feature public

  {-|
  SPL denotes the syntax of the variability language
  for FST-based feature composition.
  -}
  record SPL : Set₁ where
    constructor _◀_
    field
      root : A
      features : List Feature
  open SPL public

  {-|
  Given a configuration and a list of features,
  obtain all feature structure forests selected by
  the configuration.
  -}
  select : Configuration → List Feature → List FSF
  select _ [] = []
  select c (f ∷ fs) =
    if c (name f)
    then impl f ∷ select c fs
    else          select c fs

  names : SPL → List F
  names spl = (map name) (features spl)
```

## Feature Structure Trees are a Feature Algeba

We now prove that feature structure trees form a feature algebra.

```agda
  𝟘 : FSF
  𝟘 = [] ⊚ ([] , [])

  {-|
  Feature composition that applies
  ⊕ for lists of FSTS
  to FSFs.

  Note: ⊛ is not commutative because
        ⊕ is not commutative because
        the order in which children appear below their parents is swapped.
        Example:
        X :: a -< b >-
        Y :: a -< c >-
        X ⊕ Y = a -< b , c >-
        Y ⊕ X = a -< c , b >-
  -}
  infixr 7 _⊛_
  _⊛_ : FSF → FSF → FSF
  (l ⊚ u-l) ⊛ (r ⊚ u-r) = (l ⊕ r) ⊚ (⊕-wf u-l u-r)

  ⊛-all : List FSF → FSF
  ⊛-all = foldr _⊛_ 𝟘

  l-id : LeftIdentity _≡_ 𝟘 _⊛_
  l-id (ls ⊚ (u-ls , du-ls)) = cong-app₂ _⊚_ (⊕-idˡ ls u-ls) AllWellFormed-deterministic

  r-id : RightIdentity _≡_ 𝟘 _⊛_
  r-id (xs ⊚ (u-xs , ur-xs)) = refl

  {-|
  A predicate stating that a `P` is only true once in a list.
  In contrast to `Any`, `Once` requires a proof that `P` is false for all
  other elements in the list.
  -}
  data Once {A : Set₁} (P : A → Set) : List A → Set₁ where
    here  : {x : A} → {xs : List A} →    P x →  All (¬_ ∘ P) xs → Once P (x ∷ xs)
    there : {x : A} → {xs : List A} → ¬ (P x) → Once      P  xs → Once P (x ∷ xs)

  {-|
  Decides wether the list `xs` contains the element `y`.
  Containment is checked using `==`
  (i.e., only the root artifact is checked, all children are ignored).

  The returned predicate, in case that `y` is found in `xs`, is stronger than just containment (i.e., `Any (y ≈_)`).
  This stronger proposition is required for some proofs and
  is supported by the uniqueness constraint
  -}
  contains? : ∀ {i : Size} (xs : List (FSTA i)) (y : FSTA i)
    → Unique xs
    → y ∉ xs ⊎ Once (y ≈_) xs
  contains? [] y [] = inj₁ []
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) with y == x
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | yes y≈x = inj₂ (here y≈x (map-all (λ x≉a' y≈a' → x≉a' (≈-trans (≈-sym y≈x) y≈a')) x∉xs))
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x with contains? xs y xs-unique
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x | inj₁ y∉xs = inj₁ (y≉x ∷ y∉xs)
  contains? (x ∷ xs) y (x∉xs ∷ xs-unique) | no y≉x | inj₂ y∈x = inj₂ (there y≉x y∈x)

  ∈-⊙ˡ : ∀ {i : Size} (x : FSTA i) (ys : List (FSTA i)) (z : FSTA i)
    → x ∈ ys
    → x ∈ (ys ⊙ z)
  ∈-⊙ˡ x (y ∷ ys) z (here x≈y) with z == y
  ∈-⊙ˡ x (y ∷ ys) z (here x≈y) | no _ = here x≈y
  ∈-⊙ˡ (x -< _ >-) (.x -< _ >- ∷ ys) (.x -< _ >-) (here refl) | yes refl = here refl
  ∈-⊙ˡ x (y ∷ ys) z (there x∈ys) with z == y
  ∈-⊙ˡ x (y ∷ ys) z (there x∈ys) | no z≉y = there (∈-⊙ˡ x ys z x∈ys)
  ∈-⊙ˡ x (.z -< _ >- ∷ ys) (z -< _ >-) (there x∈ys) | yes refl = there x∈ys

  ∈-⊙ʳ : ∀ {i : Size} (x : FSTA i) (ys : List (FSTA i)) (z : FSTA i)
    → x ≈ z
    → x ∈ (ys ⊙ z)
  ∈-⊙ʳ x [] z x≈z = here x≈z
  ∈-⊙ʳ x (y ∷ ys) z x≈z with z == y
  ∈-⊙ʳ x (y ∷ ys) z x≈z | no z≉y = there (∈-⊙ʳ x ys z x≈z)
  ∈-⊙ʳ (x -< _ >-) ((.x -< _ >-) ∷ ys) (x -< _ >-) refl | yes refl = here refl

  ∈-⊙ˡ-exact : ∀ {i : Size} (x : FSTA i) (ys : List (FSTA i)) (z : FSTA i)
    → x ≉ z
    → Any (x ≡_) ys
    → Any (x ≡_) (ys ⊙ z)
  ∈-⊙ˡ-exact x (y ∷ ys) z x≉z (here x≈y) with z == y
  ∈-⊙ˡ-exact x (y ∷ ys) z x≉z (here x≈y) | no _ = here x≈y
  ∈-⊙ˡ-exact (x -< cs₁ >-) (.x -< .cs₁ >- ∷ ys) (.x -< cs₂ >-) x≉z (here refl) | yes refl = ⊥-elim (x≉z refl)
  ∈-⊙ˡ-exact x (y ∷ ys) z x≉z (there x∈ys) with z == y
  ∈-⊙ˡ-exact x (y ∷ ys) z x≉z (there x∈ys) | no z≉y = there (∈-⊙ˡ-exact x ys z x≉z x∈ys)
  ∈-⊙ˡ-exact x (.z -< _ >- ∷ ys) (z -< _ >-) x≉z (there x∈ys) | yes refl = there x∈ys

  compute-⊙-excludes : ∀ {i : Size} (x : FSTA i) (xs : List (FSTA i)) (y : FSTA i)
    → y ≉ x
    → (x ∷ xs) ⊙ y ≡ x ∷ (xs ⊙ y)
  compute-⊙-excludes x xs y y≉x with y == x
  compute-⊙-excludes x xs y y≉x | yes y≈x = ⊥-elim (y≉x y≈x)
  compute-⊙-excludes x xs y y≉x | no y≉x = refl

  compute-⊙-includes : ∀ {i : Size} (x : A) (cs₁ cs₂ : List (FSTA i)) (ys : List (FSTA (↑ i)))
    → (x -< cs₁ >- ∷ ys) ⊙ (x -< cs₂ >-) ≡ x -< cs₁ ⊕ cs₂ >- ∷ ys
  compute-⊙-includes x cs₁ cs₂ ys with x ≟ x
  compute-⊙-includes x cs₁ cs₂ ys | yes refl = refl
  compute-⊙-includes x cs₁ cs₂ ys | no x≢x = ⊥-elim (x≢x refl)

  reorder-⊙ : ∀ {i : Size} (xs : List (FSTA i)) (y z : FSTA i)
    → y ≉ z
    → z ∈ xs
    → (xs ⊙ z) ⊙ y ≡ (xs ⊙ y) ⊙ z
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs with z == x
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs | yes z≈x with y == x
  reorder-⊙ (x ∷ xs) y z y≉z z∈xs | yes z≈x | yes y≈x = ⊥-elim (y≉z (≈-trans y≈x (≈-sym z≈x)))
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ with y == (z -< cs₁ ⊕ cs₂ >-)
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ with z ≟ z
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ | yes refl = refl
  reorder-⊙ (.z -< cs₁ >- ∷ xs) y (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | no _ | no z≢z = ⊥-elim (z≢z refl)
  reorder-⊙ (.z -< cs₁ >- ∷ xs) (.z -< _ >-) (z -< cs₂ >-) y≉z z∈xs | yes refl | no _ | yes refl = ⊥-elim (y≉z refl)
  reorder-⊙ (x ∷ xs) y z y≉z (here z≈x) | no z≉x = ⊥-elim (z≉x z≈x)
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x with y == x
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ with z == x
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ | yes z≈x = ⊥-elim (z≉x z≈x)
  reorder-⊙ (x ∷ xs) y z y≉z (there z∈xs) | no z≉x | no _ | no _ = Eq.cong₂ _∷_ refl (reorder-⊙ xs y z y≉z z∈xs)
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) z y≉z (there z∈xs) | no z≉x | yes refl with z == (y -< cs₁ ⊕ cs₂ >-)
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) z y≉z (there z∈xs) | no z≉x | yes refl | no z≉y = refl
  reorder-⊙ (.y -< cs₁ >- ∷ xs) (y -< cs₂ >-) (.y -< _ >-) y≉z (there z∈xs) | no z≉a | yes refl | yes refl = ⊥-elim (y≉z refl)

  reorder-after-⊕ : ∀ {i : Size} (xs ys : List (FSTA i)) (z : FSTA i)
    → z ∈ xs
    → z ∉ ys
    → xs ⊕ (z ∷ ys) ≡ xs ⊕ (ys ⊙ z)
  reorder-after-⊕ xs [] z z∈xs [] = refl
  reorder-after-⊕ xs (y ∷ ys) z z∈xs (z≉y ∷ z∉ys) =
      xs ⊕ (z ∷ (y ∷ ys))
    ≡⟨⟩
      foldl _⊙_ xs (z ∷ y ∷ ys)
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ z) (y ∷ ys)
    ≡⟨⟩
      foldl _⊙_ ((xs ⊙ z) ⊙ y) ys
    ≡⟨⟩
      ((xs ⊙ z) ⊙ y) ⊕ ys
    ≡⟨ Eq.cong (_⊕ ys) (reorder-⊙ xs y z (≉-sym z≉y) z∈xs) ⟩
      ((xs ⊙ y) ⊙ z) ⊕ ys
    ≡⟨⟩
      (xs ⊙ y) ⊕ (z ∷ ys)
    ≡⟨ reorder-after-⊕ (xs ⊙ y) ys z (∈-⊙ˡ z xs y z∈xs) z∉ys ⟩
      xs ⊕ (y ∷ (ys ⊙ z))
    ≡⟨ Eq.cong (xs ⊕_) (compute-⊙-excludes y ys z z≉y) ⟨
      xs ⊕ ((y ∷ ys) ⊙ z)
    ∎

  ⊕-assoc : ∀ {i : Size} (xs ys zs : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → AllWellFormed zs
    → xs ⊕ (ys ⊕ zs) ≡ (xs ⊕ ys) ⊕ zs

  ⊙-⊕-distrib : {i : Size} (xs : List (FSTA (↑ i))) (y : A) (cs₁ cs₂ : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed cs₁
    → AllWellFormed cs₂
    → xs ⊙ (y -< cs₁ ⊕ cs₂ >-) ≡ (xs ⊙ (y -< cs₁ >-)) ⊙ (y -< cs₂ >-)
  ⊙-⊕-distrib [] y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf with y ≟ y
  ⊙-⊕-distrib [] y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | yes refl = refl
  ⊙-⊕-distrib [] y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | no y≢y = ⊥-elim (y≢y refl)
  ⊙-⊕-distrib (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf with (y -< cs₁ ⊕ cs₂ >-) == x
  ⊙-⊕-distrib (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | no y≉x with (y -< cs₁ >-) == x
  ⊙-⊕-distrib (x ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | no y≉x | no _ with (y -< cs₂ >-) == x
  ⊙-⊕-distrib (x ∷ xs) y cs₁ cs₂ (_ ∷ xs-unique , _ ∷ xs-wf) cs₁-wf cs₂-wf | no y≉x | no _ | no _ = Eq.cong (x ∷_) (⊙-⊕-distrib xs y cs₁ cs₂ (xs-unique , xs-wf) cs₁-wf cs₂-wf)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | no y≉x | no _ | yes refl = ⊥-elim (y≉x refl)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | no y≉x | yes refl = ⊥-elim (y≉x refl)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | yes refl with (y -< cs₁ >-) == (y -< cs >-)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | yes refl | no y≉y = ⊥-elim (y≉y refl)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | yes refl | yes refl with (y -< cs₂ >-) == (y -< cs >-)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ xs-wf cs₁-wf cs₂-wf | yes refl | yes refl | no y≉y = ⊥-elim (y≉y refl)
  ⊙-⊕-distrib (.y -< cs >- ∷ xs) y cs₁ cs₂ (_ ∷ _ , cs-wf ∷ _) cs₁-wf cs₂-wf | yes refl | yes refl | yes refl = Eq.cong (λ p → y -< p >- ∷ xs) (⊕-assoc cs cs₁ cs₂ cs-wf cs₁-wf cs₂-wf)

  ⊕-⊙-assoc-excludes : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → z ∉ ys
    → xs ⊕ (ys ⊙ z) ≡ (xs ⊕ ys) ⊙ z
  ⊕-⊙-assoc-excludes xs [] z [] = refl
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) with z == y
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) | yes z≡y = ⊥-elim (z≢y z≡y)
  ⊕-⊙-assoc-excludes xs (y ∷ ys) z (z≢y ∷ z∉ys) | no _ = ⊕-⊙-assoc-excludes (xs ⊙ y) ys z z∉ys

  ⊕-⊙-assoc-includes : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → WellFormed z
    → Once (z ≈_) ys
    → xs ⊕ (ys ⊙ z) ≡ (xs ⊕ ys) ⊙ z
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (here z≈b z∉ys) with z == y
  ⊕-⊙-assoc-includes xs (.z -< cs₁ >- ∷ ys) (z -< cs₂ >-) xs-wf (_ , cs₁-wf ∷ _) z-wf (here z≈b z∉ys) | yes refl =
      xs ⊕ (z -< cs₁ ⊕ cs₂ >- ∷ ys)
    ≡⟨⟩
      foldl _⊙_ xs (z -< cs₁ ⊕ cs₂ >- ∷ ys)
    ≡⟨⟩
      foldl _⊙_ (xs ⊙ (z -< cs₁ ⊕ cs₂ >-)) ys
    ≡⟨⟩
      (xs ⊙ (z -< cs₁ ⊕ cs₂ >-)) ⊕ ys
    ≡⟨ Eq.cong (λ x → foldl _⊙_ x ys) (⊙-⊕-distrib xs z cs₁ cs₂ xs-wf cs₁-wf z-wf) ⟩
      ((xs ⊙ z -< cs₁ >-) ⊙ (z -< cs₂ >-)) ⊕ ys
    ≡⟨⟩
      (xs ⊙ z -< cs₁ >-) ⊕ (z -< cs₂ >- ∷ ys)
    ≡⟨ reorder-after-⊕ (xs ⊙ z -< cs₁ >-) ys (z -< cs₂ >-) (∈-⊙ʳ (z -< cs₂ >-) xs (z -< cs₁ >-) refl) z∉ys ⟩
      (xs ⊙ z -< cs₁ >-) ⊕ (ys ⊙ z -< cs₂ >-)
    ≡⟨ ⊕-⊙-assoc-excludes (xs ⊙ z -< cs₁ >-) ys (z -< cs₂ >-) z∉ys ⟩
      ((xs ⊙ z -< cs₁ >-) ⊕ ys) ⊙ (z -< cs₂ >-)
    ≡⟨⟩
      (foldl _⊙_ (xs ⊙ z -< cs₁ >-) ys) ⊙ (z -< cs₂ >-)
    ≡⟨⟩
      (foldl _⊙_ xs (z -< cs₁ >- ∷ ys)) ⊙ (z -< cs₂ >-)
    ≡⟨⟩
      (xs ⊕ (z -< cs₁ >- ∷ ys)) ⊙ (z -< cs₂ >-)
    ∎
  ⊕-⊙-assoc-includes xs (y -< cs₁ >- ∷ ys) (z -< cs₂ >-) xs-wf ys-wf z-wf (here z≈b z∉ys) | no z≉b = ⊥-elim (z≉b z≈b)
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (there z≉b z∉ys) with z == y
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf ys-wf z-wf (there z≉b z∉ys) | yes z≈b = ⊥-elim (z≉b z≈b)
  ⊕-⊙-assoc-includes xs (y ∷ ys) z xs-wf (_ ∷ ys-unique , b-wf ∷ ys-wf) z-wf (there z≉b z∉ys) | no _ = ⊕-⊙-assoc-includes (xs ⊙ y) ys z (⊙-wf xs-wf b-wf) (ys-unique , ys-wf) z-wf z∉ys

  ⊕-⊙-assoc : ∀ {i : Size} (xs ys : List (FSTA i)) (z : (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → WellFormed z
    → foldl _⊙_ xs (ys ⊙ z) ≡ foldl _⊙_ xs ys ⊙ z
  ⊕-⊙-assoc xs ys z xs-wf (ys-unique , ys-wf) z-wf =
    Sum.[ ⊕-⊙-assoc-excludes xs ys z
        , ⊕-⊙-assoc-includes xs ys z xs-wf (ys-unique , ys-wf) z-wf
        ]′ (contains? ys z ys-unique)

  -- ⊕-assoc : ∀ {i : Size} (xs ys zs : List (FSTA i))
  --   → AllWellFormed xs
  --   → AllWellFormed ys
  --   → AllWellFormed zs
  --   → xs ⊕ (ys ⊕ zs) ≡ (xs ⊕ ys) ⊕ zs
  ⊕-assoc xs ys [] xs-wf ys-wf zs-wf = refl
  ⊕-assoc xs ys (z ∷ zs) xs-wf ys-wf (_ ∷ zs-unique , z-wf ∷ zs-wf) =
      xs ⊕ (ys ⊕ (z ∷ zs))
    ≡⟨⟩
      xs ⊕ foldl _⊙_ ys (z ∷ zs)
    ≡⟨⟩
      xs ⊕ foldl _⊙_ (ys ⊙ z) zs
    ≡⟨⟩
      xs ⊕ ((ys ⊙ z) ⊕ zs)
    ≡⟨ ⊕-assoc xs (ys ⊙ z) zs xs-wf (⊙-wf ys-wf z-wf) (zs-unique , zs-wf) ⟩
      (xs ⊕ (ys ⊙ z)) ⊕ zs
    ≡⟨ Eq.cong (λ x → foldl _⊙_ x zs) (⊕-⊙-assoc xs ys z xs-wf ys-wf z-wf) ⟩
      ((xs ⊕ ys) ⊙ z) ⊕ zs
    ≡⟨⟩
      foldl _⊙_ ((xs ⊕ ys) ⊙ z) zs
    ≡⟨⟩
      foldl _⊙_ (xs ⊕ ys) (z ∷ zs)
    ≡⟨⟩
      (xs ⊕ ys) ⊕ (z ∷ zs)
    ∎

  assoc : Associative _≡_ _⊛_
  assoc (x ⊚ x-wf) (y ⊚ y-wf) (z ⊚ z-wf) = cong-app₂ _⊚_ (Eq.sym (⊕-assoc x y z x-wf y-wf z-wf)) AllWellFormed-deterministic

  cong : Congruent₂ _≡_ _⊛_
  cong refl refl = refl

  ⊕-idem : ∀ {i : Size} (xs ys : List (FSTA i))
    → AllWellFormed xs
    → AllWellFormed ys
    → xs ⊕ ys ⊕ xs ≡ xs ⊕ ys

  ⊕-direct-idem : {i : Size} → (xs : List (FSTA i)) → AllWellFormed xs → xs ⊕ xs ≡ xs
  ⊕-direct-idem xs (xs-unique , xs-wf) =
      xs ⊕ xs
    ≡⟨ Eq.cong₂ _⊕_ refl (⊕-idˡ xs xs-unique) ⟨
      xs ⊕ ([] ⊕ xs)
    ≡⟨ ⊕-idem xs [] (xs-unique , xs-wf) ([] , []) ⟩
      xs ⊕ []
    ≡⟨⟩
      xs
    ∎

  ⊙-idem : ∀ {i : Size} (xs : List (FSTA i)) (y : FSTA i)
    → Unique xs
    → WellFormed y
    → Any (y ≡_) xs
    → xs ⊙ y ≡ xs
  ⊙-idem (.y ∷ xs) y xs-unique y-wf (here refl) with y == y
  ⊙-idem (.y ∷ xs) y xs-unique y-wf (here refl) | no y≉y = ⊥-elim (y≉y ≈-refl)
  ⊙-idem (.(y -< cs >-) ∷ xs) (y -< cs >-) xs-unique y-wf (here refl) | yes refl = Eq.cong₂ _∷_ (Eq.cong₂ _-<_>- refl (⊕-direct-idem cs y-wf)) refl
  ⊙-idem (x ∷ xs) y (_ ∷ xs-unique) y-wf (there y∈xs) with y == x
  ⊙-idem (x ∷ xs) y (_ ∷ xs-unique) y-wf (there y∈xs) | no y≉a = Eq.cong₂ _∷_ refl (⊙-idem xs y xs-unique y-wf y∈xs)
  ⊙-idem (.y -< _ >- ∷ xs) (y -< _ >-) (y∉xs ∷ _) y-wf (there y∈xs) | yes refl = ⊥-elim (All.All¬⇒¬Any y∉xs (Any.map (λ where {(_ -< _ >-)} refl → refl) y∈xs))

  ⊙-⊕-distrib-idem : {i : Size} (xs : List (FSTA (↑ i))) (z : A) (cs₁ cs₂ : List (FSTA i))
    → Unique xs
    → AllWellFormed cs₁
    → AllWellFormed cs₂
    → Any ((z -< cs₂ >-) ≡_) xs
    → xs ⊙ (z -< cs₁ ⊕ cs₂ >-) ≡ xs ⊙ (z -< cs₁ >-)
  ⊙-⊕-distrib-idem (x ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (there z∈xs) with (z -< cs₁ ⊕ cs₂ >-) == x
  ⊙-⊕-distrib-idem (x ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (there z∈xs) | no z≉x with (z -< cs₁ >-) == x
  ⊙-⊕-distrib-idem (x ∷ xs) z cs₁ cs₂ (_ ∷ xs-unique) cs₁-wf cs₂-wf (there z∈xs) | no z≉x | no _ = Eq.cong₂ _∷_ refl (⊙-⊕-distrib-idem xs z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf z∈xs)
  ⊙-⊕-distrib-idem (.z -< _ >- ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (there z∈xs) | no z≉x | yes refl = ⊥-elim (z≉x refl)
  ⊙-⊕-distrib-idem (.z -< _ >- ∷ xs) z cs₁ cs₂ (x∉xs ∷ _) cs₁-wf cs₂-wf (there z∈xs) | yes refl = ⊥-elim (All.All¬⇒¬Any x∉xs (Any.map (λ where {(_ -< _ >-)} refl → refl) z∈xs))
  ⊙-⊕-distrib-idem (.z -< _ >- ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (here refl) with z ≟ z
  ⊙-⊕-distrib-idem (.z -< _ >- ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (here refl) | yes refl =
      (z -< cs₂ ⊕ (cs₁ ⊕ cs₂) >-) ∷ xs
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong₂ _-<_>- refl (⊕-idem cs₂ cs₁ cs₂-wf cs₁-wf)) refl ⟩
      (z -< cs₂ ⊕ cs₁ >-) ∷ xs
    ∎
  ⊙-⊕-distrib-idem (.z -< _ >- ∷ xs) z cs₁ cs₂ xs-unique cs₁-wf cs₂-wf (here refl) | no z≢z = ⊥-elim (z≢z refl)

  ⊙-distant-idempotence : ∀ {i : Size} (xs ys : List (FSTA i)) (z : FSTA i)
    → AllWellFormed xs
    → AllWellFormed ys
    → WellFormed z
    → Any (z ≡_) xs
    → xs ⊕ (ys ⊙ z) ≡ xs ⊕ ys
  ⊙-distant-idempotence xs [] z (xs-unique , _) ys-wf z-wf z∈xs = ⊙-idem xs z xs-unique z-wf z∈xs
  ⊙-distant-idempotence xs (y ∷ ys) z xs-wf ys-wf z-wf z∈xs with z == y
  ⊙-distant-idempotence xs (y ∷ ys) z xs-wf (_ ∷ ys-unique , y-wf ∷ ys-wf) z-wf z∈xs | no z≉y = ⊙-distant-idempotence (xs ⊙ y) ys z (⊙-wf xs-wf y-wf) (ys-unique , ys-wf) z-wf (∈-⊙ˡ-exact z xs y z≉y z∈xs)
  ⊙-distant-idempotence xs (.z -< cs₁ >- ∷ ys) (z -< cs₂ >-) (xs-unique , _) (_ , y-wf ∷ _) z-wf z∈xs | yes refl = Eq.cong (_⊕ ys) (⊙-⊕-distrib-idem xs z cs₁ cs₂ xs-unique y-wf z-wf z∈xs)

  ⊕-++-idem : ∀ {i : Size} (xs₁ xs₂ ys : List (FSTA i))
    → AllWellFormed (xs₁ ++ xs₂)
    → AllWellFormed ys
    → (xs₁ ++ xs₂) ⊕ (ys ⊕ xs₂) ≡ (xs₁ ++ xs₂) ⊕ ys
  ⊕-++-idem xs₁ [] ys xs-wf ys-wf = refl
  ⊕-++-idem xs₁ (x ∷ xs₂) ys (xs-unique , xs-wf) ys-wf =
      (xs₁ ++ (x ∷ xs₂)) ⊕ (ys ⊕ (x ∷ xs₂))
    ≡⟨⟩
      (xs₁ ++ (x ∷ xs₂)) ⊕ foldl _⊙_ ys (x ∷ xs₂)
    ≡⟨⟩
      (xs₁ ++ (x ∷ xs₂)) ⊕ foldl _⊙_ (ys ⊙ x) xs₂
    ≡⟨⟩
      foldl _⊙_ (xs₁ ++ (x ∷ xs₂)) (foldl _⊙_ (ys ⊙ x) xs₂)
    ≡⟨⟩
      (xs₁ ++ (x ∷ xs₂)) ⊕ ((ys ⊙ x) ⊕ xs₂)
    ≡⟨ Eq.cong (_⊕ ((ys ⊙ x) ⊕ xs₂)) (List.∷ʳ-++ xs₁ x xs₂) ⟨
      ((xs₁ ∷ʳ x) ++ xs₂) ⊕ ((ys ⊙ x) ⊕ xs₂)
    ≡⟨ ⊕-++-idem (xs₁ ∷ʳ x) xs₂ (ys ⊙ x) (Eq.subst AllWellFormed (Eq.sym (List.∷ʳ-++ xs₁ x xs₂)) (xs-unique , xs-wf)) (⊙-wf ys-wf (All.head (All.++⁻ʳ xs₁ xs-wf))) ⟩
      ((xs₁ ∷ʳ x) ++ xs₂) ⊕ (ys ⊙ x)
    ≡⟨ Eq.cong (_⊕ (ys ⊙ x)) (List.∷ʳ-++ xs₁ x xs₂) ⟩
      (xs₁ ++ (x ∷ xs₂)) ⊕ (ys ⊙ x)
    ≡⟨ ⊙-distant-idempotence (xs₁ ++ (x ∷ xs₂)) ys x (xs-unique , xs-wf) ys-wf (All.head (All.++⁻ʳ xs₁ xs-wf)) (Any.++⁺ʳ xs₁ (here refl)) ⟩
      (xs₁ ++ (x ∷ xs₂)) ⊕ ys
    ∎

  -- ⊕-idem : ∀ {i : Size} (xs ys : List (FSTA i))
  --   → AllWellFormed xs
  --   → AllWellFormed ys
  --   → xs ⊕ ys ⊕ xs ≡ xs ⊕ ys
  ⊕-idem xs ys xs-wf ys-wf = ⊕-++-idem [] xs ys xs-wf ys-wf

  idem : ∀ (x y : FSF) → x ⊛ y ⊛ x ≡ x ⊛ y
  idem (x ⊚ x-wf) (y ⊚ y-wf) = cong-app₂ _⊚_ (⊕-idem x y x-wf y-wf) AllWellFormed-deterministic

  {-|
  Finally, we conclude that feature structure forests form a feature algreba.
  -}
  FST-is-FeatureAlgebra : FeatureAlgebra FSF _⊛_ 𝟘
  FST-is-FeatureAlgebra = record
    { monoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = cong
          }
        ; assoc = assoc
        }
      ; identity = l-id , r-id
      }
    ; distant-idempotence = idem
    }
    where
      open import Data.Product using (_,_)
```

## Semantics

```agda
  {-|
  Semantics of FST product lines.
  Given a configuration c, select all FSFs whose feature is selected by c.
  Then compose all those features.
  Finally, drop the uniqueness-typing to obtain a single variant.
  -}
  ⟦_⟧ : SPL → Configuration → Rose ∞ AtomSet
  ⟦ r ◀ features ⟧ c = r -< forget-uniqueness (⊛-all (select c features)) >-
```

## Show

```agda
  open import Data.String using (String; _<+>_)
  open import Vatras.Show.Lines hiding (map)

  module Show (show-F : F → String) (show-A : A → String) where
    mutual
      show-FST : {i : Size} → FSTA i → Lines
      show-FST (a -< cs >-) = do
        > show-A a
        indent 2 (lines (map show-FST cs))

      show-FSF : {i : Size} → List (FSTA i) → Lines
      show-FSF roots = lines (map show-FST roots)

      show-Feature : Feature → Lines
      show-Feature feature = do
        > show-F (name feature) <+> "∷"
        indent 2 (show-FSF (forget-uniqueness (impl feature)))
```

## Feature Structure Trees are a Variability Language

```agda
⟦_⟧ : 𝔼-Semantics (Rose ∞) Configuration Impose.SPL
⟦_⟧ {A} = Impose.⟦_⟧ A

FSTL : VariabilityLanguage (Rose ∞)
FSTL = ⟪ Impose.SPL , Configuration , ⟦_⟧ ⟫
```
