{-# OPTIONS --allow-unsolved-metas #-}

module Framework.V2.Lang.FST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; _because_; False)
open import Relation.Binary using (DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Definitions
open import Framework.V2.Variants using (artifact)
open import Framework.V2.Annotation.Name using (Name)
open import Framework.V2.Constructs.Artifact
open import Framework.V2.Lang.FeatureAlgebra

Conf : (N : 𝔽) → Set
Conf N = Config N Bool

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

module Defs {A : 𝔸} (_≟_ : DecidableEquality A) where
  data FST : Set
  record FSF : Set
  different : Rel FST 0ℓ

  data FST where
    node : A → FSF → FST

  different (node a _) (node b _) = False (a ≟ b)

  -- Feature Structure Forest
  infix 4 ⟪_,_⟫
  record FSF where
    inductive
    constructor ⟪_,_⟫
    field
      roots : List FST
      no-duplicates : AllPairs different roots

  infixr 3 _::_
  record Feature (N : 𝔽) : Set where
    constructor _::_
    field
      name : Name N
      impl : FSF
  open Feature public

-- the syntax used in the paper for paths
  infixr 5 _．_[_]
  _．_[_] : A → (cs : List FST) → AllPairs different cs → FSF
  a ． cs [ d ] = ⟪ node a ⟪ cs , d ⟫ ∷ [] , [] ∷ [] ⟫

  -- helper function when branching in paths
  branches : List (List FST) → List FST
  branches = concat

  SPL : (N : 𝔽) → Set --𝔼
  SPL N  = List (Feature N)

  select : ∀ {N} → Conf N → SPL N → SPL N
  select c = filterᵇ (c ∘ name)

  forget-names : ∀ {N} → SPL N → List FSF
  forget-names = map impl

  names : ∀ {N} → SPL N → List N
  names = map name

  map-different : ∀ {b xs} →
    ∀ (ys : FSF) (z : FST)
    → different (node b xs) z
    → different (node b ys) z
  map-different {b} _ (node z _) l with z ≟ b
  ... | yes _ = l
  ... | no  _ = l

  map-all-different : ∀ {b cs cs' xs}
    → All (different (node b cs )) xs
    → All (different (node b cs')) xs
  map-all-different [] = []
  map-all-different {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-different cs' x px ∷ map-all-different pxs

  open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)
  open Eq.≡-Reasoning

  𝟘 : FSF
  𝟘 = ⟪ [] , [] ⟫

  mutual
    data PlainFST : Set where
      pnode : A → List PlainFST → PlainFST
    foo = pnode

    pdifferent : Rel PlainFST 0ℓ
    pdifferent (pnode a _) (pnode b _) = False (a ≟ b)

    Unique : List PlainFST → Set
    Unique = AllPairs pdifferent

    UniqueNode : PlainFST → Set
    UniqueNode (pnode _ as) = UniqueR as

    UniqueR : List PlainFST → Set
    UniqueR cs = Unique cs × All UniqueNode cs

    data UFST : Set where
      unode : A → (cs : List UFST) → AllPairs udifferent cs → UFST

    udifferent : Rel UFST 0ℓ
    udifferent (unode a _ _) (unode b _ _) = False (a ≟ b)

    forget-unique : UFST -> PlainFST
    forget-unique (unode a cs _) = pnode a (map forget-unique cs)

    map-pdifferent : ∀ {b xs} (ys : List PlainFST) (z : PlainFST)
      → pdifferent (foo b xs) z
      → pdifferent (foo b ys) z
    map-pdifferent {b} _ (pnode z _) l with z ≟ b
    ... | yes _ = l
    ... | no  _ = l

    map-all-pdifferent : ∀ {b cs cs' xs}
      → All (pdifferent (foo b cs )) xs
      → All (pdifferent (foo b cs')) xs
    map-all-pdifferent [] = []
    map-all-pdifferent {cs' = cs'} {xs = x ∷ xs} (px ∷ pxs) = map-pdifferent cs' x px ∷ map-all-pdifferent pxs

    infix 4 _+_⟶_
    data _+_⟶_ : PlainFST → List (PlainFST) → List (PlainFST) → Set where
      base : ∀ {l : PlainFST}
          ---------------
        → l + [] ⟶ l ∷ []

      merge : ∀ {a as bs rs cs}
        → as + bs ↝ cs
          ----------------------------------------------
        → pnode a as + pnode a bs ∷ rs ⟶ pnode a cs ∷ rs

      skip : ∀ {a as b bs rs cs}
        → ¬ (a ≡ b)
        → pnode a as + rs ⟶ cs
          ----------------------------------------------
        → pnode a as + pnode b bs ∷ rs ⟶ pnode b bs ∷ cs

    infix 4 _+_↝_
    data _+_↝_ : List PlainFST → List PlainFST → List PlainFST → Set where
      impose-nothing : ∀ {rs}
        → [] + rs ↝ rs

      impose-step : ∀ {l ls rs e e'}
        → l  + rs ⟶ e'
        → ls + e' ↝ e
          ----------------
        → l ∷ ls + rs ↝ e

    ↝-deterministic : ∀ {fs rs e e'}
      → fs + rs ↝ e
      → fs + rs ↝ e'
      → e ≡ e'
    ↝-deterministic impose-nothing impose-nothing = refl
    ↝-deterministic (impose-step ⟶x ↝x) (impose-step ⟶y ↝y) rewrite ⟶-deterministic ⟶x ⟶y | ↝-deterministic ↝x ↝y = refl

    ⟶-deterministic : ∀ {f rs e e'}
      → f + rs ⟶ e
      → f + rs ⟶ e'
      → e ≡ e'
    ⟶-deterministic base base = refl
    ⟶-deterministic (merge x) (merge y) rewrite ↝-deterministic x y = refl
    ⟶-deterministic (merge x) (skip a≠a y) = ⊥-elim (a≠a refl)
    ⟶-deterministic (skip a≠a x) (merge y) = ⊥-elim (a≠a refl)
    ⟶-deterministic (skip neq x) (skip neq' y) rewrite ⟶-deterministic x y = refl

    ↝-return : ∀ {e ls rs}
      → ls + rs ↝ e
      → ∃[ e ] (ls + rs ↝ e)
    ↝-return {e} ↝e = e , ↝e

    ⟶-return : ∀ {e l rs}
      → l + rs ⟶ e
      → ∃[ e ] (l + rs ⟶ e)
    ⟶-return {e} ⟶e = e , ⟶e

    ↝-total : ∀ (ls rs : List PlainFST) → ∃[ e ] (ls + rs ↝ e)
    ↝-total [] rs = ↝-return impose-nothing
    ↝-total (l ∷ ls) rs =
      let e' , ⟶e' = ⟶-total l rs
          _  , ↝e  = ↝-total ls e'
       in ↝-return (impose-step ⟶e' ↝e)

    ⟶-total : ∀ (l : PlainFST) (rs : List PlainFST) → ∃[ e ] (l + rs ⟶ e)
    ⟶-total l [] = ⟶-return base
    ⟶-total (pnode a as) (pnode b bs ∷ rs) with a ≟ b
    ... | yes refl =
      let cs , ↝cs = ↝-total as bs
       in ⟶-return (merge ↝cs)
    ... | no  a≠b =
      let cs , ⟶cs = ⟶-total (pnode a as) rs
       in ⟶-return (skip a≠b ⟶cs)

    map-Unique-head : ∀ {a as bs rs}
      → Unique (foo a as ∷ rs)
      → Unique (foo a bs ∷ rs)
    map-Unique-head (x ∷ xs) = map-all-pdifferent x ∷ xs

    drop-second-Unique : ∀ {x y zs}
      → Unique (x ∷ y ∷ zs)
      → Unique (x ∷ zs)
    drop-second-Unique ((_ ∷ pxs) ∷ _ ∷ zs) = pxs ∷ zs

    head-Unique : ∀ {x xs}
      → Unique (x ∷ xs)
      → All (pdifferent x) xs
    head-Unique (x ∷ xs) = x

    -- Observation: We can actually generalize this to any All, not just Unique!
    impose-nothing-preserves-unique : ∀ {rs e : List PlainFST}
      → [] + rs ↝ e
      → Unique rs
      → Unique e
    impose-nothing-preserves-unique impose-nothing u-rs = u-rs

    ↝-preserves-unique : ∀ {ls rs e : List PlainFST}
      → ls + rs ↝ e
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ↝-preserves-unique impose-nothing ur-ls ur-rs = ur-rs
    ↝-preserves-unique {pnode a as ∷ ls} {rs} (impose-step {e' = e'} ⟶e' ↝e) (u-l ∷ u-ls , ur-as ∷ ur-ls) ur-rs =
      let ur-e' = ⟶-preserves-unique a as rs e' ⟶e' ur-as ur-rs
          ur-e  = ↝-preserves-unique ↝e (u-ls , ur-ls) ur-e'
       in ur-e

    ⟶-preserves-unique : ∀ (a : A) (ls rs : List PlainFST) (e : List PlainFST)
      → foo a ls + rs ⟶ e -- Bug in Agda here: replacing foo by pnode breaks
      → UniqueR ls
      → UniqueR rs
      → UniqueR e
    ⟶-preserves-unique _ _ _ _ base ur-ls _ = [] ∷ [] , ur-ls ∷ []
    ⟶-preserves-unique a ls (pnode .a bs ∷ rs) e@(pnode .a cs ∷ rs) (merge ↝e) ur-ls (u-rs , ur-bs ∷ un-rs)
      = map-Unique-head u-rs , ↝-preserves-unique ↝e ur-ls ur-bs ∷ un-rs
    ⟶-preserves-unique a ls (pnode b bs ∷ rs) (pnode .b .bs ∷ cs) (skip a≠b ⟶cs) u-ls (u-r ∷ u-rs , ur-bs ∷ ur-rs)
      = induction a≠b (u-r ∷ u-rs) ⟶cs ∷ u-cs , ur-bs ∷ un-cs
      where
        ur-cs = ⟶-preserves-unique a ls rs cs ⟶cs u-ls (u-rs , ur-rs)
        u-cs = proj₁ ur-cs
        un-cs = proj₂ ur-cs

        induction : ∀ {a ls rs cs b bs}
          → ¬ (a ≡ b)
          → Unique (foo b bs ∷ rs)
          → foo a ls + rs ⟶ cs
          → All (pdifferent (foo b bs)) cs
        induction a≠b _     base     = False-sym _≟_ (≠→False _≟_ a≠b) ∷ []
        induction a≠b u-rs (merge _) = False-sym _≟_ (≠→False _≟_ a≠b) ∷ head-Unique (drop-second-Unique u-rs)
        induction a≠b ((b≠b' ∷ u-r) ∷ _ ∷ u-rs) (skip a≠b' ⟶cs) = b≠b' ∷ induction a≠b (u-r ∷ u-rs) ⟶cs

    -- TODO: Avoid termination macro.
    {-# TERMINATING #-}
    impose-subtree : FST → FSF → FSF
    impose-subtree l ⟪ [] , no-duplicates ⟫ = ⟪ l ∷ [] , [] ∷ [] ⟫
    impose-subtree (node a ⟪ as , υ-as ⟫) ⟪ node b ⟪ bs , υ-bs ⟫ ∷ rs , υ-b ∷ υ-rs ⟫ with a ≟ b
    ... | yes _ = ⟪ node b (⟪ as , υ-as ⟫ ⊕ ⟪ bs , υ-bs ⟫) ∷ rs , map-all-different υ-b ∷ υ-rs ⟫
    ... | no ¬p =
      ⟪ node b ⟪ bs , υ-bs ⟫ ∷ r-rec , helpi (different-values a b ⟪ as , υ-as ⟫ ⟪ bs , υ-bs ⟫ ¬p) υ-b ∷ υ-rec ⟫
      where
        rec = impose-subtree (node a ⟪ as , υ-as ⟫) ⟪ rs , υ-rs ⟫
        r-rec = FSF.roots rec
        υ-rec = FSF.no-duplicates rec

        ¬-sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → ¬ (a ≡ b) → ¬ (b ≡ a)
        ¬-sym ¬a≡b b≡a = ¬a≡b (Eq.sym b≡a)

        different-values : ∀ (a b : A) (xs ys : FSF)
          → ¬ (a ≡ b)
          → different (node a xs) (node b ys)
        different-values a b _ _ neq with a ≟ b
        ... | yes eq = neq eq
        ... | no neq = tt

        open import Data.Empty using (⊥; ⊥-elim)
        open import Relation.Nullary.Decidable using (isYes)
        different-sym : ∀ {a b}
          → different a b
          → different b a
        different-sym {node a as} {node b bs} neq with b ≟ a
        ... | no neq = tt
        ... | yes eq = {!!}

        helpi : ∀ {na nb} {xs : List FST} {υ-xs : AllPairs different xs}
          → different na nb
          → All (different nb) xs
          → All (different nb) (FSF.roots (impose-subtree na ⟪ xs , υ-xs ⟫))
        helpi {na} {nb} na≠nb [] = different-sym {na} {nb} na≠nb ∷ []
        helpi {node a as} {node b bs} {x ∷ xs} {υ-x ∷ υ-xs} na≠nb (px ∷ pxs) with a ≟ b
        ... | yes _ = {!!}
        ... | no _ = {!!}
    -- impose-subtree l ⟪ [] , _ ⟫ = l ∷ []
    -- impose-subtree (node a ⟪ as , as-unique ⟫) ⟪ node b ⟪ bs , bs-unique ⟫ ∷ rs , _ ⟫ with a ≟ b
    -- ... | yes _ = node b ? ∷ rs
    -- ... | no  _ = node b ⟪ bs , bs-unique ⟫ ∷ impose-subtree (node a ⟪ as , as-unique ⟫) rs

    infixr 7 _⊕_
    _⊕_ : FSF → FSF → FSF
    ⟪ l , _ ⟫ ⊕ r = foldr impose-subtree r l

  ⊕-all : List FSF → FSF
  ⊕-all = foldr _⊕_ 𝟘

  l-id : LeftIdentity _≡_ 𝟘 _⊕_
  l-id _ = refl

  -- This is not satisfied. What did we do wrong?
  -- I think the problem is that (x ∷ xs) ⊕ 𝟘
  -- denotes an FST superimposition of x onto xs, recursively,
  -- which is not what we want.
  -- What happens is that
  -- 1.) x gets imposed onto 𝟘 and yields x
  -- 2.) the next child in xs gets imposed onto x, potentially mutating x.
  -- BOOM
  -- TODO: How to fix that? This self-imposition also occurs when the rhs is not 𝟘.
  --       So it is normal, right?
  --       Maybe, the imposition should not be done sequentially but in parallel?
  r-id : RightIdentity _≡_ 𝟘 _⊕_
  r-id = {!!}
    -- rewrite r-id xs =
    -- begin
    --   impose-subtree x xs
    -- ≡⟨ {!!} ⟩
    --   x ∷ xs
    -- ∎

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

  ⟦_⟧ : ∀ {N : 𝔽} → SPL N → Conf N → FSF
  ⟦ features ⟧ c = (⊕-all ∘ forget-names ∘ select c) features

  -- We could avoid wrap and unwrap by defining our own intermediate tree structure
  -- that does not reuse Artifact constructor.
  -- unwrap : Rose A → Artifact A (Rose A)
  -- unwrap (artifact a) = a

  -- wrap : Artifact A (Rose A) → Rose A
  -- wrap a = artifact a

  open import Data.String using (String; _<+>_)
  open import Show.Lines

  module Show {N : 𝔽} (show-N : N → String) (show-A : A → String) where
    mutual
      -- TODO: Why does termination checking fail here?
      {-# TERMINATING #-}
      show-FST : FST → Lines
      show-FST (node a ⟪ children , uniq ⟫) = do
        > show-A a
        indent 2 (show-FSF ⟪ children , uniq ⟫)

      show-FSF : FSF → Lines
      show-FSF fst = lines (map (show-FST) (FSF.roots fst))

      show-Feature : Feature N → Lines
      show-Feature feature = do
        > show-N (name feature) <+> "∷"
        indent 2 (show-FSF (impl feature))
