{-# OPTIONS --allow-unsolved-metas #-}

module Framework.V2.Lang.FST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Function using (_∘_)
open import Level using (0ℓ)

open import Relation.Nullary.Decidable using (yes; no; False)
open import Relation.Binary using (DecidableEquality; Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Definitions
open import Framework.V2.Variants using (artifact)
open import Framework.V2.Annotation.Name using (Name)
open import Framework.V2.Constructs.Artifact
open import Framework.V2.Lang.FeatureAlgebra

-- data FSTNode : 𝕍 where
--   -- add a proof that the children are disjoint wrt. ≡
--   node : ∀ {A} → A → List (FSTNode A) → FSTNode A

Conf : (N : 𝔽) → Set
Conf N = Config N Bool

module Defs {A : 𝔸} (_≟_ : DecidableEquality A) where
  data FSTNode : Set
  different : Rel FSTNode 0ℓ

  data FSTNode where
    node : A → (children : List FSTNode) → AllPairs different children → FSTNode

  different (node a _ _) (node b _ _) = False (a ≟ b)

  -- All FSTs have the same implicit root.
  -- So an FST is just a list of children, implicitly grouped below
  -- an imaginary unique root.
  FST : Set
  FST = List FSTNode

  infixr 4 _::_
  record Feature (N : 𝔽) : Set where
    constructor _::_
    field
      name : Name N
      impl : FST
  open Feature public

-- the syntax used in the paper for paths
  infixr 5 _．_[_]
  _．_[_] : A → (cs : List FSTNode) → AllPairs different cs → FST
  a ． cs [ d ] = node a cs d ∷ []

  -- helper function when branching in paths
  branches : List (List FSTNode) → List FSTNode
  branches = concat

  -- Feature Structure Forest
  FSF : (N : 𝔽) → Set --𝔼
  FSF N  = List (Feature N)

  select : ∀ {N} → Conf N → FSF N → FSF N
  select c = filterᵇ (c ∘ name)

  forget-names : ∀ {N} → FSF N → List FST
  forget-names = map impl

  names : ∀ {N} → FSF N → List N
  names = map name

  open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)
  open Eq.≡-Reasoning

  𝟘 : FST
  𝟘 = []

  mutual
    -- TODO: Avoid termination macro.
    {-# TERMINATING #-}
    impose-subtree : FSTNode → List FSTNode → List FSTNode
    impose-subtree l [] = l ∷ []
    impose-subtree (node a as as-unique) (node b bs bs-unique ∷ rs) with a ≟ b
    ... | yes _ = node b (as ⊕ bs) {!!} ∷ rs
    ... | no  _ = node b bs bs-unique ∷ impose-subtree (node a as as-unique) rs

    infixr 7 _⊕_
    _⊕_ : FST → FST → FST
    l ⊕ r = foldr impose-subtree r l

  ⊕-all : List FST → FST
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
  r-id [] = refl
  r-id (x ∷ xs) = {!!}
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

  idem : ∀ (i₁ i₂ : FST) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂
  idem = {!!}

  FST-is-FeatureAlgebra : FeatureAlgebra FST _⊕_ 𝟘
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

  ⟦_⟧ : ∀ {N : 𝔽} → FSF N → Conf N → FST
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
      show-FSTNode : FSTNode → Lines
      show-FSTNode (node a children _) = do
        > show-A a
        indent 2 (show-FST children)

      show-FST : FST → Lines
      show-FST fst = lines (map show-FSTNode fst)

      show-Feature : Feature N → Lines
      show-Feature feature = do
        > show-N (name feature) <+> "∷"
        indent 2 (show-FST (impl feature))
