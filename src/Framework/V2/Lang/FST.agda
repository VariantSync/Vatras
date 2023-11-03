module Framework.V2.Lang.FST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat)
open import Function using (_∘_)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no)

open import Framework.V2.Definitions
open import Framework.V2.Variants using (artifact)
open import Framework.V2.Annotation.Name using (Name)
open import Framework.V2.Constructs.Artifact
open import Framework.V2.Lang.FeatureAlgebra

data FSTNode : 𝕍 where
  node : ∀ {A} → A → List (FSTNode A) → FSTNode A

-- All FSTs have the same implicit root.
-- So an FST is just a list of children, implicitly grouped below
-- an imaginary unique root.
FST : 𝕍
FST A = List (FSTNode A)

infixr 4 _::_
record Feature (N : 𝔽) (A : 𝔸) : Set where
  constructor _::_
  field
    name : Name N
    impl : FST A
open Feature public

-- the syntax used in the paper for paths
infixr 5 _．_
_．_ : ∀ {A : 𝔸} → A → List (FSTNode A) → FST A
a ． cs = node a cs ∷ []

-- helper function when branching in paths
branches : ∀ {A : 𝔸} → List (List (FSTNode A)) → List (FSTNode A)
branches = concat

FeatureForest : (N : 𝔽) → 𝔼
FeatureForest N A = List (Feature N A)

Conf : (N : 𝔽) → Set
Conf N = Config N Bool

select : ∀ {N A} → Conf N → FeatureForest N A → FeatureForest N A
select c = filterᵇ (c ∘ name)

forget-names : ∀ {N A} → FeatureForest N A → List (FST A)
forget-names = map impl

names : ∀ {N A} → FeatureForest N A → List N
names = map name

module Algebra {A : 𝔸} (_≟_ : DecidableEquality A) where
  𝟘 : FST A
  𝟘 = []

  mutual
    -- TODO: Avoid termination macro.
    {-# TERMINATING #-}
    impose-subtree : FSTNode A → List (FSTNode A) → List (FSTNode A)
    impose-subtree l [] = l ∷ []
    impose-subtree (node a as) (node b bs ∷ rs) with a ≟ b
    ... | yes _ = node b (as ⊕ bs) ∷ rs
    ... | no  _ = node b bs ∷ impose-subtree (node a as) rs

    infixr 7 _⊕_
    _⊕_ : FST A → FST A → FST A
    l ⊕ r = foldr impose-subtree r l

    ⊕-all : List (FST A) → FST A
    ⊕-all = foldr _⊕_ 𝟘

    -- FST-is-FeatureAlgebra : FeatureAlgebra (FST A) _⊕_ 𝟘
    -- FST-is-FeatureAlgebra = {!!}

    ⟦_⟧ : ∀ {N : 𝔽} → FeatureForest N A → Conf N → FST A
    ⟦ features ⟧ c = (⊕-all ∘ forget-names ∘ select c) features

    -- We could avoid wrap and unwrap by defining our own intermediate tree structure
    -- that does not reuse Artifact constructor.
    -- unwrap : Rose A → Artifact A (Rose A)
    -- unwrap (artifact a) = a

    -- wrap : Artifact A (Rose A) → Rose A
    -- wrap a = artifact a

open import Data.String using (String; _<+>_)
open import Show.Lines

module Show {N : 𝔽} {A : 𝔸} (show-N : N → String) (show-A : A → String) where
  mutual
    -- TODO: Why does termination checking fail here?
    {-# TERMINATING #-}
    show-FSTNode : FSTNode A → Lines
    show-FSTNode (node a children) = do
      > show-A a
      indent 2 (show-FST children)

    show-FST : FST A → Lines
    show-FST fst = lines (map show-FSTNode fst)

    show-Feature : Feature N A → Lines
    show-Feature feature = do
      > show-N (name feature) <+> "∷"
      indent 2 (show-FST (impl feature))
