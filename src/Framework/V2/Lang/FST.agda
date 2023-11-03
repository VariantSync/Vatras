open import Framework.V2.Definitions
open import Relation.Binary using (DecidableEquality)

module Framework.V2.Lang.FST
  (A : 𝔸)
  (_≟_ : DecidableEquality A)
  where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; foldr; map)

open import Relation.Nullary.Decidable using (_because_)

open import Framework.V2.Variants using (Rose; artifact)
open import Framework.V2.Annotation.Name using (Name)
open import Framework.V2.Constructs.Artifact
open import Framework.V2.Lang.FeatureAlgebra

FeaturePath : Set → Set
FeaturePath = List

data FST : 𝕍 where
  root : ∀ {A : 𝔸} → List (Rose A) → FST A

FeatureForest : (N : Set) → 𝔼
FeatureForest N A = ∀ (n : Name N) → FeaturePath A

𝟘 : FST A
𝟘 = root []

-- We could avoid wrap and unwrap by defining our own intermediate tree structure
-- that does not reuse Artifact constructor.
unwrap : Rose A → Artifact A (Rose A)
unwrap (artifact a) = a

wrap : Artifact A (Rose A) → Rose A
wrap a = artifact a

mutual
    -- TODO: Avoid termination macro.
    {-# TERMINATING #-}
    impose-subtree : Artifact A (Rose A) → List (Artifact A (Rose A)) → List (Artifact A (Rose A))
    impose-subtree l [] = l ∷ []
    impose-subtree (a -< as >-) (b -< bs >- ∷ rs) with a ≟ b
    ... | true  because _ = b -< impose as bs >- ∷ rs
    ... | false because _ = impose-subtree (a -< as >-) rs

    impose-raw : List (Artifact A (Rose A)) → List (Artifact A (Rose A)) → List (Artifact A (Rose A))
    impose-raw ls rs = foldr impose-subtree rs ls

    impose : List (Rose A) → List (Rose A) → List (Rose A)
    impose ls rs = map wrap (impose-raw (map unwrap ls) (map unwrap rs))

infixr 7 _⊕_
_⊕_ : FST A → FST A → FST A
root l ⊕ root r = root (impose l r)

-- FST-is-FeatureAlgebra : FeatureAlgebra (FST A) _⊕_ 𝟘
-- FST-is-FeatureAlgebra = {!!}
