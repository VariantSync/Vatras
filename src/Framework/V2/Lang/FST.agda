{-# OPTIONS --allow-unsolved-metas #-}

module Framework.V2.Lang.FST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; map; filterᵇ; concat)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to map-all)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_; head)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
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

module Defs {A : 𝔸} where
  data PlainFST : Set where
    pnode : A → List PlainFST → PlainFST

  -- the syntax used in the paper for paths
  infixr 5 _．_
  _．_ : A → (cs : List PlainFST) → List PlainFST
  a ． cs = pnode a cs ∷ []

  -- helper function when branching in paths
  branches : List (List PlainFST) → List PlainFST
  branches = concat

  mutual
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

    -- This is bascially just a fold on lists. Maybe we can simplify it accordingly.
    infix 4 _+_↝_
    data _+_↝_ : List PlainFST → List PlainFST → List PlainFST → Set where
      impose-nothing : ∀ {rs}
        → [] + rs ↝ rs

      impose-step : ∀ {l ls rs e e'}
        → l  + rs ⟶ e'
        → ls + e' ↝ e
          ----------------
        → l ∷ ls + rs ↝ e

  mutual
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

  module Impose (_≟_ : DecidableEquality A) where

    mutual
      --- TODO: Fix termination checking
      {-# TERMINATING #-}
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

    pdifferent : Rel PlainFST 0ℓ
    pdifferent (pnode a _) (pnode b _) = False (a ≟ b)

    map-pdifferent : ∀ {b xs} (ys : List PlainFST) (z : PlainFST)
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

    Unique : List PlainFST → Set
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
      data UniqueNode : PlainFST → Set where
        unq : ∀ {a cs} → UniqueR cs → UniqueNode (pnode a cs)

      UniqueR : List PlainFST → Set
      UniqueR cs = Unique cs × All UniqueNode cs

    mutual
      ↝-preserves-unique : ∀ {ls rs e : List PlainFST}
        → ls + rs ↝ e
        → UniqueR ls
        → UniqueR rs
        → UniqueR e
      ↝-preserves-unique impose-nothing ur-ls ur-rs = ur-rs
      ↝-preserves-unique {pnode a as ∷ ls} {rs} (impose-step {e' = e'} ⟶e' ↝e) (u-l ∷ u-ls , unq ur-as ∷ ur-ls) ur-rs =
        let ur-e' = ⟶-preserves-unique a as rs e' ⟶e' ur-as ur-rs
            ur-e  = ↝-preserves-unique ↝e (u-ls , ur-ls) ur-e'
         in ur-e

      ⟶-preserves-unique : ∀ (a : A) (ls rs : List PlainFST) (e : List PlainFST)
        → pnode a ls + rs ⟶ e
        → UniqueR ls
        → UniqueR rs
        → UniqueR e
      ⟶-preserves-unique _ _ _ _ base ur-ls _ = [] ∷ [] , (unq ur-ls) ∷ []
      ⟶-preserves-unique a ls (pnode .a bs ∷ rs) e@(pnode .a cs ∷ rs) (merge ↝e) ur-ls (u-rs , (unq ur-bs) ∷ un-rs)
        = unique-ignores-children u-rs , unq (↝-preserves-unique ↝e ur-ls ur-bs) ∷ un-rs
      ⟶-preserves-unique a ls (pnode b bs ∷ rs) (pnode .b .bs ∷ cs) (skip a≠b ⟶cs) u-ls (u-r ∷ u-rs , ur-bs ∷ ur-rs)
        = induction a≠b (u-r ∷ u-rs) ⟶cs ∷ u-cs , ur-bs ∷ un-cs
        where
          ur-cs = ⟶-preserves-unique a ls rs cs ⟶cs u-ls (u-rs , ur-rs)
          u-cs = proj₁ ur-cs
          un-cs = proj₂ ur-cs

          induction : ∀ {a ls rs cs b bs}
            → ¬ (a ≡ b)
            → Unique (pnode b bs ∷ rs)
            → pnode a ls + rs ⟶ cs
            → All (pdifferent (pnode b bs)) cs
          induction a≠b _     base     = False-sym _≟_ (≠→False _≟_ a≠b) ∷ []
          induction a≠b u-rs (merge _) = False-sym _≟_ (≠→False _≟_ a≠b) ∷ head (drop-second-Unique u-rs)
          induction a≠b ((b≠b' ∷ u-r) ∷ _ ∷ u-rs) (skip a≠b' ⟶cs) = b≠b' ∷ induction a≠b (u-r ∷ u-rs) ⟶cs

    ---- SPL Stuff ----

    -- Feature Structure Forest
    FSF : Set
    FSF = Σ (List PlainFST) UniqueR

    forget-uniqueness : FSF → List PlainFST
    forget-uniqueness = proj₁

    infixr 3 _::_
    record Feature (N : 𝔽) : Set where
      constructor _::_
      field
        name : Name N
        impl : FSF
    open Feature public

    SPL : (N : 𝔽) → Set --𝔼
    SPL N  = List (Feature N)

    select : ∀ {N} → Conf N → SPL N → SPL N
    select c = filterᵇ (c ∘ name)

    forget-names : ∀ {N} → SPL N → List FSF
    forget-names = map impl

    names : ∀ {N} → SPL N → List N
    names = map name

    ---- Algebra ----
    open import Algebra.Definitions using (LeftIdentity; RightIdentity; Associative; Congruent₂)
    open Eq.≡-Reasoning

    𝟘 : FSF
    𝟘 = [] , [] , []

    infixr 7 _⊕_
    _⊕_ : FSF → FSF → FSF
    (l , u-l) ⊕ (r , u-r) =
      let e , ↝e = ↝-total l r
          u-e    = ↝-preserves-unique ↝e u-l u-r
       in e , u-e

    ⊕-all : List FSF → FSF
    ⊕-all = foldr _⊕_ 𝟘

    l-id : LeftIdentity _≡_ 𝟘 _⊕_
    l-id _ = refl

    r-id : RightIdentity _≡_ 𝟘 _⊕_
    r-id ([] , [] , []) = refl
    r-id (.(pnode _ _) ∷ [] , [] ∷ [] , unq x ∷ []) = refl
    r-id (x ∷ y ∷ zs , u-x ∷ u-y ∷ u-zs , ur-x ∷ ur-y ∷ ur-zs) = {!!}

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
        show-FST : PlainFST → Lines
        show-FST (pnode a children) = do
          > show-A a
          indent 2 (show-FSF children)

        show-FSF : List PlainFST → Lines
        show-FSF roots = lines (map show-FST roots)

        show-Feature : Feature N → Lines
        show-Feature feature = do
          > show-N (name feature) <+> "∷"
          indent 2 (show-FSF (forget-uniqueness (impl feature)))
