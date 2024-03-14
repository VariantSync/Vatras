{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Lang.FST (F : 𝔽) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat; reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Size using (∞)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Annotation.Name using (Name)
open import Framework.Variants using (Rose; rose)
open import Framework.Composition.FeatureAlgebra
open import Construct.Artifact

Conf : Set
Conf = F → Bool

module TODO-MOVE-TO-AUX-OR-USE-STL where
  ≠-sym : ∀ {ℓ} {A : Set ℓ} (a b : A)
    → ¬ (a ≡ b)
    → ¬ (b ≡ a)
  ≠-sym a b a≠b refl = a≠b refl

  ≠→False : ∀ {ℓ} {A : Set ℓ} {a b : A}
    → (_≟_ : DecidableEquality A)
    → ¬ (a ≡ b)
    → False (a ≟ b)
  ≠→False {a = a} {b = b} _≟_ a≠b with a ≟ b
  ... | yes a≡b = ⊥-elim (a≠b a≡b)
  ... | no    _ = tt

  False-sym : ∀ {ℓ} {A : Set ℓ} {a b : A}
    → (_≟_ : DecidableEquality A)
    → False (a ≟ b)
    → False (b ≟ a)
  False-sym {a = a} {b = b} _≟_ _ with a ≟ b
  ... | no ¬p = ≠→False _≟_ (≠-sym a b ¬p)
open TODO-MOVE-TO-AUX-OR-USE-STL

data FST : 𝔼 where
  pnode : ∀ {A : 𝔸} → A → List (FST A) → FST A

induction : ∀ {A : 𝔸} {B : Set} → (A → List B → B) → FST A → B
induction {A} {B} f n = go n [] where
  go : FST A → List B → B
  go (pnode a []) bs = f a (reverse bs)
  go (pnode a (c ∷ cs)) bs = go (pnode a cs) (go c [] ∷ bs)

toVariant : ∀ {A} → FST A → Rose ∞ A
toVariant {A} = induction step
  module toVariant-implementation where
  step : A → List (Rose ∞ A) → Rose ∞ A
  step a cs = rose (a -< cs >-)

-- the syntax used in the paper for paths
infixr 5 _．_
_．_ : ∀ {A} → A → (cs : List (FST A)) → List (FST A)
a ． cs = pnode a cs ∷ []

-- helper function when branching in paths
branches : ∀ {A} → List (List (FST A)) → List (FST A)
branches = concat

mutual
  infix 4 _+_⟶_
  data _+_⟶_ : ∀ {A} → FST A → List (FST A) → List (FST A) → Set where
    base : ∀ {A} {l : FST A}
        ---------------
      → l + [] ⟶ l ∷ []

    merge : ∀ {A} {a : A} {as bs rs cs : List (FST A)}
      → as + bs ↝ cs
        ----------------------------------------------
      → pnode a as + pnode a bs ∷ rs ⟶ pnode a cs ∷ rs

    skip : ∀ {A} {a b : A} {as bs rs cs : List (FST A)}
      → ¬ (a ≡ b)
      → pnode a as + rs ⟶ cs
        ----------------------------------------------
      → pnode a as + pnode b bs ∷ rs ⟶ pnode b bs ∷ cs

  -- This is basically just a fold on lists. Maybe we can simplify it accordingly.
  infix 4 _+_↝_
  data _+_↝_ : ∀ {A} → List (FST A) → List (FST A) → List (FST A) → Set where
    impose-nothing : ∀ {A} {rs : List (FST A)}
      → [] + rs ↝ rs

    impose-step : ∀ {A} {l : FST A} {ls rs e e' : List (FST A)}
      → l  + rs ⟶ e'
      → ls + e' ↝ e
        ----------------
      → l ∷ ls + rs ↝ e

mutual
  ↝-deterministic : ∀ {A} {fs rs e e' : List (FST A)}
    → fs + rs ↝ e
    → fs + rs ↝ e'
    → e ≡ e'
  ↝-deterministic impose-nothing impose-nothing = refl
  ↝-deterministic (impose-step ⟶x ↝x) (impose-step ⟶y ↝y) rewrite ⟶-deterministic ⟶x ⟶y | ↝-deterministic ↝x ↝y = refl

  ⟶-deterministic : ∀ {A} {f : FST A} {rs e e' : List (FST A)}
    → f + rs ⟶ e
    → f + rs ⟶ e'
    → e ≡ e'
  ⟶-deterministic base base = refl
  ⟶-deterministic (merge x) (merge y) rewrite ↝-deterministic x y = refl
  ⟶-deterministic (merge x) (skip a≠a y) = ⊥-elim (a≠a refl)
  ⟶-deterministic (skip a≠a x) (merge y) = ⊥-elim (a≠a refl)
  ⟶-deterministic (skip neq x) (skip neq' y) rewrite ⟶-deterministic x y = refl

↝-return : ∀ {A} {e ls rs : List (FST A)}
  → ls + rs ↝ e
  → ∃[ e ] (ls + rs ↝ e)
↝-return {e = e} ↝e = e , ↝e

⟶-return : ∀ {A} {l : FST A} {e rs : List (FST A)}
  → l + rs ⟶ e
  → ∃[ e ] (l + rs ⟶ e)
⟶-return {e = e} ⟶e = e , ⟶e

module Impose {A : 𝔸} (_≟_ : DecidableEquality A) where
  childs : FST A → List (FST A)
  childs (pnode a as) = as

  mutual
    ↝-total : ∀ (ls rs : List (FST A)) → ∃[ e ] (ls + rs ↝ e)
    ↝-total [] rs = ↝-return impose-nothing
    ↝-total (pnode a as ∷ ls) rs =
      let e' , ⟶e' = ⟶-total (pnode a as) rs (↝-total as)
          _  , ↝e  = ↝-total ls e'
      in ↝-return (impose-step ⟶e' ↝e)

    ⟶-total : ∀ (l : FST A) (rs : List (FST A)) → ((rs' : List (FST A)) → ∃[ e ] (childs l + rs' ↝ e)) → ∃[ e ] (l + rs ⟶ e)
    ⟶-total l [] _ = ⟶-return base
    ⟶-total (pnode a as) (pnode b bs ∷ rs) ↝-total-as with a ≟ b
    ... | yes refl =
      let cs , ↝cs = ↝-total-as bs
      in ⟶-return (merge ↝cs)
    ... | no  a≠b =
      let cs , ⟶cs = ⟶-total (pnode a as) rs ↝-total-as
      in ⟶-return (skip a≠b ⟶cs)

  pdifferent : Rel (FST A) 0ℓ
  pdifferent (pnode a _) (pnode b _) = False (a ≟ b)

  map-pdifferent : ∀ {b xs} (ys : List (FST A)) (z : FST A)
    → pdifferent (pnode b xs) z
    → pdifferent (pnode b ys) z
  map-pdifferent {b} _ (pnode z _) l with z ≟ b
  ... | yes _ = l
  ... | no  _ = l

  map-all-pdifferent : ∀ {b cs cs' xs}
    → All (pdifferent (pnode b cs )) xs
    → All (pdifferent (pnode b cs')) xs
  map-all-pdifferent [] = []
  map-all-pdifferent {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-pdifferent cs' x px ∷ map-all-pdifferent pxs

  Unique : List (FST A) → Set
  Unique = AllPairs pdifferent

  unique-ignores-children : ∀ {a as bs rs}
    → Unique (pnode a as ∷ rs)
    → Unique (pnode a bs ∷ rs)
  unique-ignores-children (x ∷ xs) = map-all-pdifferent x ∷ xs

  drop-second-Unique : ∀ {x y zs}
    → Unique (x ∷ y ∷ zs)
    → Unique (x ∷ zs)
  drop-second-Unique ((_ ∷ pxs) ∷ _ ∷ zs) = pxs ∷ zs

  mutual
    data UniqueNode : FST A → Set where
      unq : ∀ {a cs} → UniqueR cs → UniqueNode (pnode a cs)

    UniqueR : List (FST A) → Set
    UniqueR cs = Unique cs × All UniqueNode cs

  mutual
    ↝-preserves-unique : ∀ {ls rs e : List (FST A)}
      → ls + rs ↝ e
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ↝-preserves-unique impose-nothing ur-ls ur-rs = ur-rs
    ↝-preserves-unique {pnode a as ∷ ls} {rs} (impose-step {e' = e'} ⟶e' ↝e) (u-l ∷ u-ls , unq ur-as ∷ ur-ls) ur-rs =
      let ur-e' = ⟶-preserves-unique a as rs e' ⟶e' ur-as ur-rs
          ur-e  = ↝-preserves-unique ↝e (u-ls , ur-ls) ur-e'
       in ur-e

    ⟶-preserves-unique : ∀ (a : A) (ls rs : List (FST A)) (e : List (FST A))
      → pnode a ls + rs ⟶ e
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ⟶-preserves-unique _ _ _ _ base ur-ls _ = [] ∷ [] , (unq ur-ls) ∷ []
    ⟶-preserves-unique a ls (pnode .a bs ∷ rs) e@(pnode .a cs ∷ rs) (merge ↝e) ur-ls (u-rs , (unq ur-bs) ∷ un-rs)
      = unique-ignores-children u-rs , unq (↝-preserves-unique ↝e ur-ls ur-bs) ∷ un-rs
    ⟶-preserves-unique a ls (pnode b bs ∷ rs) (pnode .b .bs ∷ cs) (skip a≠b ⟶cs) u-ls (u-r ∷ u-rs , ur-bs ∷ ur-rs)
      = ind a≠b (u-r ∷ u-rs) ⟶cs ∷ u-cs , ur-bs ∷ un-cs
      where
        ur-cs = ⟶-preserves-unique a ls rs cs ⟶cs u-ls (u-rs , ur-rs)
        u-cs = proj₁ ur-cs
        un-cs = proj₂ ur-cs

        ind : ∀ {a ls rs cs b bs}
          → ¬ (a ≡ b)
          → Unique (pnode b bs ∷ rs)
          → pnode a ls + rs ⟶ cs
          → All (pdifferent (pnode b bs)) cs
        ind a≠b _     base     = False-sym _≟_ (≠→False _≟_ a≠b) ∷ []
        ind a≠b u-rs (merge _) = False-sym _≟_ (≠→False _≟_ a≠b) ∷ head (drop-second-Unique u-rs)
        ind a≠b ((b≠b' ∷ u-r) ∷ _ ∷ u-rs) (skip a≠b' ⟶cs) = b≠b' ∷ ind a≠b (u-r ∷ u-rs) ⟶cs

  -- Feature Structure Forest
  record FSF : Set where
    constructor _⊚_
    field
      trees : List (FST A)
      valid : UniqueR trees
  open FSF public

  forget-uniqueness : FSF → List (FST A)
  forget-uniqueness = trees

  toVariants : FSF → List (Rose ∞ A)
  toVariants = map toVariant ∘ trees

  {-
  A feature is a named feature structure tree.
  All features in a product line are required to have
  the very same root node, otherwise they could not be
  imposed.
  To ensure this constraint by design, this root node is
  part of the SPL definition and not the feature.
  Hence, a feature is a rootless tree: It holds a list of trees,
  which denote the children of the common root.
  -}
  infixr 3 _::_
  record Feature : Set where
    constructor _::_
    field
      name : Name F
      impl : FSF
  open Feature public

  record SPL : Set where
    constructor _◀_
    field
      root : A
      features : List Feature
  open SPL public

  select : Conf → List Feature → List Feature
  select c = filterᵇ (c ∘ name)

  -- forget-names : ∀ {N} → SPL N → List FSF
  -- forget-names = map impl

  names : SPL → List F
  names = map name ∘ features

  ---- Algebra ----
  open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)
  open Eq.≡-Reasoning

  𝟘 : FSF
  𝟘 = [] ⊚ ([] , [])

  infixr 7 _⊕_
  _⊕_ : FSF → FSF → FSF
  (l ⊚ u-l) ⊕ (r ⊚ u-r) =
    let e , ↝e = ↝-total l r
        u-e    = ↝-preserves-unique ↝e u-l u-r
     in e ⊚ u-e

  ⊕-all : List FSF → FSF
  ⊕-all = foldr _⊕_ 𝟘

  ⟦_⟧ : SPL → Conf → Rose ∞ A
  ⟦ r ◀ features ⟧ c = rose (r -< toVariants (⊕-all (map impl (select c features))) >-)

  l-id : LeftIdentity _≡_ 𝟘 _⊕_
  l-id _ = refl

  r-id : RightIdentity _≡_ 𝟘 _⊕_
  r-id = {!!}
  -- r-id ([] ⊚ ([] , [])) = refl
  -- r-id (.(pnode _ _) ∷ [] , [] ∷ [] , unq x ∷ []) = refl
  -- r-id (x ∷ y ∷ zs , u-x ∷ u-y ∷ u-zs , ur-x ∷ ur-y ∷ ur-zs) = {!!}

  assoc : Associative _≡_ _⊕_
  assoc x y z = {!!}

  cong : Congruent₂ _≡_ _⊕_
  cong refl refl = refl

  idem : ∀ (i₁ i₂ : FSF) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂
  idem = {!!}

  FST-is-FeatureAlgebra : FeatureAlgebra FSF _⊕_ 𝟘
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

  -- We could avoid wrap and unwrap by defining our own intermediate tree structure
  -- that does not reuse Artifact constructor.
  -- unwrap : Rose A → Artifact A (Rose A)
  -- unwrap (artifact a) = a

  -- wrap : Artifact A (Rose A) → Rose A
  -- wrap a = artifact a

  open import Data.String using (String; _<+>_)
  open import Show.Lines

  module Show (show-F : F → String) (show-A : A → String) where
    mutual
      show-FST : FST A → Lines
      show-FST = induction λ a children → do
        > show-A a
        indent 2 (lines children)

      show-FSF : List (FST A) → Lines
      show-FSF roots = lines (map show-FST roots)

      show-Feature : Feature → Lines
      show-Feature feature = do
        > show-F (name feature) <+> "∷"
        indent 2 (show-FSF (forget-uniqueness (impl feature)))
