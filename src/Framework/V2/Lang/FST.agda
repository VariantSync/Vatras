{-# OPTIONS --allow-unsolved-metas #-}

module Framework.V2.Lang.FST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Level using (0ℓ)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; False)
open import Relation.Binary using (DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Definitions
open import Framework.V2.Variants using (artifact)
open import Framework.V2.Annotation.Name using (Name)
open import Framework.V2.Constructs.Artifact
open import Framework.V2.Lang.FeatureAlgebra

Conf : (N : 𝔽) → Set
Conf N = Config N Bool

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

    pdifferent : Rel PlainFST 0ℓ
    pdifferent (pnode a _) (pnode b _) = False (a ≟ b)

    infix 4 _+_⟶_
    data _+_⟶_ : PlainFST → List (PlainFST) → List (PlainFST) → Set where
      base : ∀ {l}
          ----------
        → l + [] ⟶ l ∷ []

      merge : ∀ {a as bs rs cs}
        → as + bs ↝ cs
        → pnode a as + pnode a bs ∷ rs ⟶ pnode a cs ∷ rs

      skip : ∀ {a as b bs rs cs}
        → ¬ (a ≡ b)
        → pnode a as + rs ⟶ cs
        → pnode a as + pnode b bs ∷ rs ⟶ pnode b bs ∷ cs

    infix 4 _+_↝_
    data _+_↝_ : List PlainFST → List PlainFST → List PlainFST → Set where
      impose-nothing : ∀ {rs}
        → [] + rs ↝ rs

      impose-step : ∀ {l ls rs e e'}
        → l  + rs ⟶ e
        → ls + e  ↝ e'
          ----------------
        → l ∷ ls + rs ↝ e'

    Unique : List PlainFST → Set
    Unique = AllPairs pdifferent

    ↝-deterministic : ∀ {fs rs e e'}
      → fs + rs ↝ e
      → fs + rs ↝ e'
      → e ≡ e'
    ↝-deterministic impose-nothing impose-nothing = refl
    ↝-deterministic (impose-step ⟶x ↝x) (impose-step ⟶y ↝y) rewrite ⟶-deterministic ⟶x ⟶y | ↝-deterministic ↝x ↝y = refl

    open import Data.Empty using (⊥; ⊥-elim)
    ⟶-deterministic : ∀ {f rs e e'}
      → f + rs ⟶ e
      → f + rs ⟶ e'
      → e ≡ e'
    ⟶-deterministic base base = refl
    ⟶-deterministic (merge x) (merge y) rewrite ↝-deterministic x y = refl
    ⟶-deterministic (merge x) (skip a≠a y) = ⊥-elim (a≠a refl)
    ⟶-deterministic (skip a≠a x) (merge y) = ⊥-elim (a≠a refl)
    ⟶-deterministic (skip neq x) (skip neq' y) rewrite ⟶-deterministic x y = refl

    open import Data.Product using (∃-syntax; _,_)
    ↝-total : ∀ (ls rs : List PlainFST) → ∃[ e ] (ls + rs ↝ e)
    ↝-total [] rs = rs , impose-nothing
    ↝-total (l ∷ ls) rs = {!!} , {!!}

    ⟶-total : ∀ (l : PlainFST) (rs : List PlainFST) → ∃[ e ] (l + rs ⟶ e)
    ⟶-total l [] = {!!}
    ⟶-total l (x ∷ rs) = {!!}

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
